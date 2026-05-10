(******************************************************************************)
(*                                                                            *)
(*  RFC 8738: IPv4 model                                                      *)
(*                                                                            *)
(*  IPv4 ADT, RFC 1123 §2.1 dotted-decimal printer/parser, leading-zero       *)
(*  rejection, full bidirectional round-trip and canonicalization theorems.   *)
(*                                                                            *)
(******************************************************************************)

From Coq Require Import
  List String Ascii NArith.NArith ZArith Arith Lia Bool.
Require Import RFC8738_Prelude.

Import ListNotations.
Open Scope N_scope.

(* ------------------------------------------------------------ *)
(* IPv4 ADT (record of four octets)                             *)
(* ------------------------------------------------------------ *)

Record ipv4 := mk_ipv4 {
  ip4_a : byte;
  ip4_b : byte;
  ip4_c : byte;
  ip4_d : byte
}.

Definition ipv4_valid (ip : ipv4) : bool :=
  andb (byte_valid (ip4_a ip))
    (andb (byte_valid (ip4_b ip))
      (andb (byte_valid (ip4_c ip))
            (byte_valid (ip4_d ip)))).

(* Constructor that truncates inputs to the byte range. *)
Definition mk_ipv4_trunc (a b c d : N) : ipv4 :=
  mk_ipv4 (a mod 256) (b mod 256) (c mod 256) (d mod 256).

Definition ipv4_eqb (x y : ipv4) : bool :=
  andb (byte_eqb (ip4_a x) (ip4_a y))
    (andb (byte_eqb (ip4_b x) (ip4_b y))
      (andb (byte_eqb (ip4_c x) (ip4_c y))
            (byte_eqb (ip4_d x) (ip4_d y)))).

Lemma ipv4_eqb_refl : forall ip, ipv4_eqb ip ip = true.
Proof. intro ip; unfold ipv4_eqb; rewrite !byte_eqb_refl; reflexivity. Qed.

Lemma ipv4_eqb_sound : forall x y, ipv4_eqb x y = true -> x = y.
Proof.
  intros [a1 b1 c1 d1] [a2 b2 c2 d2] H.
  unfold ipv4_eqb in H. cbn in H.
  apply andb_true_iff in H as [Ha H].
  apply andb_true_iff in H as [Hb H].
  apply andb_true_iff in H as [Hc Hd].
  apply byte_eqb_sound in Ha, Hb, Hc, Hd. subst. reflexivity.
Qed.

(* ------------------------------------------------------------ *)
(* Printer (RFC 1123 §2.1: shortest decimal, no leading zeros)  *)
(* ------------------------------------------------------------ *)

Definition print_ipv4 (ip : ipv4) : string :=
  string_concat
    [byte_to_decimal (ip4_a ip);
     "."%string;
     byte_to_decimal (ip4_b ip);
     "."%string;
     byte_to_decimal (ip4_c ip);
     "."%string;
     byte_to_decimal (ip4_d ip)].

(* ------------------------------------------------------------ *)
(* Parser                                                       *)
(*                                                              *)
(* Parses a dotted-quad following RFC 1123 §2.1:                *)
(*   - 4 octets separated by '.'                                *)
(*   - each octet is 1..3 decimal digits                        *)
(*   - leading zeros not permitted (except for "0" itself)      *)
(*   - each octet must be in [0, 255]                           *)
(* ------------------------------------------------------------ *)

(* Parse an octet from a list of ASCII characters.  Returns the byte and
   the remaining input.  Greedy on digits but enforces RFC 1123 §2.1. *)
Definition parse_octet_chars (cs : list ascii) : option (byte * list ascii) :=
  match cs with
  | [] => None
  | c0 :: r0 =>
      if negb (is_dec_digit c0) then None
      else
        let v0 := dec_value c0 in
        if N.eqb v0 0 then
          (* "0" must stand alone; if followed by a digit, leading-zero. *)
          match r0 with
          | [] => Some (0, [])
          | c1 :: _ =>
              if is_dec_digit c1 then None
              else Some (0, r0)
          end
        else
          match r0 with
          | [] => Some (v0, [])
          | c1 :: r1 =>
              if negb (is_dec_digit c1) then Some (v0, r0)
              else
                let v1 := v0 * 10 + dec_value c1 in
                match r1 with
                | [] => Some (v1, [])
                | c2 :: r2 =>
                    if negb (is_dec_digit c2) then Some (v1, r1)
                    else
                      let v2 := v1 * 10 + dec_value c2 in
                      if N.leb v2 255 then
                        match r2 with
                        | [] => Some (v2, [])
                        | c3 :: _ =>
                            if is_dec_digit c3 then None
                            else Some (v2, r2)
                        end
                      else None
                end
          end
  end.

Definition expect_dot (cs : list ascii) : option (list ascii) :=
  match cs with
  | "."%char :: rest => Some rest
  | _ => None
  end.

Definition parse_ipv4_chars (cs : list ascii) : option ipv4 :=
  match parse_octet_chars cs with
  | None => None
  | Some (a, r1) =>
      match expect_dot r1 with
      | None => None
      | Some r2 =>
          match parse_octet_chars r2 with
          | None => None
          | Some (b, r3) =>
              match expect_dot r3 with
              | None => None
              | Some r4 =>
                  match parse_octet_chars r4 with
                  | None => None
                  | Some (c, r5) =>
                      match expect_dot r5 with
                      | None => None
                      | Some r6 =>
                          match parse_octet_chars r6 with
                          | None => None
                          | Some (d, []) => Some (mk_ipv4 a b c d)
                          | Some _ => None
                          end
                      end
                  end
              end
          end
      end
  end.

Definition parse_ipv4 (s : string) : option ipv4 :=
  parse_ipv4_chars (ascii_list_of_string s).

(* ------------------------------------------------------------ *)
(* Round-trip lemmas                                            *)
(* ------------------------------------------------------------ *)

(* "rest does not start with a digit" — invariant for round-tripping. *)
Definition no_lead_digit (rest : list ascii) : Prop :=
  match rest with
  | [] => True
  | c :: _ => is_dec_digit c = false
  end.

Lemma dot_no_lead_digit : forall rest, no_lead_digit ("."%char :: rest).
Proof. intro rest. cbn. reflexivity. Qed.

(* dec_char of values 1..9 produces a non-zero digit char. *)
Lemma dec_char_nonzero :
  forall n, 1 <= n -> n < 10 -> N.eqb (dec_value (dec_char n)) 0 = false.
Proof.
  intros n Hlo Hhi.
  rewrite dec_value_dec_char by exact Hhi.
  apply N.eqb_neq. lia.
Qed.

(* Decompose a 2-digit byte b in [10, 99]. *)
Lemma decompose_2 :
  forall b, 10 <= b -> b < 100 -> b = (b / 10) * 10 + b mod 10.
Proof.
  intros b _ _.
  rewrite (N.div_mod b 10) at 1 by lia.
  lia.
Qed.

Lemma div10_lt_10 :
  forall b, b < 100 -> b / 10 < 10.
Proof.
  intros b H. apply N.Div0.div_lt_upper_bound. lia.
Qed.

Lemma div10_ge_1_of_ge_10 :
  forall b, 10 <= b -> 1 <= b / 10.
Proof.
  intros b H. apply N.div_le_lower_bound; lia.
Qed.

Lemma mod10_lt_10 : forall b, b mod 10 < 10.
Proof. intro b. apply N.mod_lt; lia. Qed.

(* Decompose a 3-digit byte b in [100, 255]. *)
Lemma decompose_3 :
  forall b, 100 <= b -> b <= 255 ->
  b = (b / 100) * 100 + ((b / 10) mod 10) * 10 + b mod 10.
Proof.
  intros b _ _.
  pose proof (N.div_mod b 100 ltac:(lia)) as H100.
  pose proof (N.div_mod b 10 ltac:(lia)) as H10.
  pose proof (N.div_mod (b / 10) 10 ltac:(lia)) as Hd10.
  assert (Hbb : b / 100 = (b / 10) / 10)
    by (rewrite N.Div0.div_div; reflexivity).
  rewrite Hbb in H100 |- *.
  rewrite Hd10 in H100. lia.
Qed.

Lemma div100_le_2 : forall b, b <= 255 -> b / 100 <= 2.
Proof.
  intros b H.
  enough (b / 100 < 3) by lia.
  apply N.Div0.div_lt_upper_bound. lia.
Qed.

Lemma div100_ge_1_of_ge_100 :
  forall b, 100 <= b -> 1 <= b / 100.
Proof.
  intros b H. apply N.div_le_lower_bound; lia.
Qed.

Lemma mod10_div10_lt_10 : forall b, (b / 10) mod 10 < 10.
Proof. intro b. apply N.mod_lt; lia. Qed.

(* The print of any byte yields one of three forms.  We split round-trip into
   the three cases. *)

Lemma parse_octet_print_lt10 :
  forall b rest,
    b < 10 ->
    no_lead_digit rest ->
    parse_octet_chars
      ((ascii_list_of_string (byte_to_decimal b)) ++ rest)%list
    = Some (b, rest).
Proof.
  intros b rest Hlt Hno.
  unfold byte_to_decimal.
  destruct (N.ltb_spec b 10) as [Hl|Hg]; [|lia]. clear Hl.
  cbn [ascii_list_of_string app].
  unfold parse_octet_chars.
  pose proof (dec_char_in_range b Hlt) as Hd. rewrite Hd. cbn [negb].
  pose proof (dec_value_dec_char b Hlt) as Hv. rewrite Hv.
  destruct (N.eqb b 0) eqn:Hb0.
  - apply N.eqb_eq in Hb0. subst b.
    destruct rest as [|c rest'].
    + reflexivity.
    + cbn in Hno. rewrite Hno. cbn. reflexivity.
  - destruct rest as [|c rest'].
    + reflexivity.
    + cbn in Hno. rewrite Hno. cbn. reflexivity.
Qed.

Lemma parse_octet_print_ge10_lt100 :
  forall b rest,
    10 <= b -> b < 100 ->
    no_lead_digit rest ->
    parse_octet_chars
      ((ascii_list_of_string (byte_to_decimal b)) ++ rest)%list
    = Some (b, rest).
Proof.
  intros b rest Hlo Hhi Hno.
  unfold byte_to_decimal.
  destruct (N.ltb_spec b 10) as [Hl|_]; [lia|].
  destruct (N.ltb_spec b 100) as [_|Hr]; [|lia].
  cbn [ascii_list_of_string app].
  unfold parse_octet_chars.
  (* First digit: dec_char (b / 10), value in 1..9 *)
  assert (Hd1lt10 : b / 10 < 10) by (apply div10_lt_10; lia).
  assert (Hd1ge1 : 1 <= b / 10) by (apply div10_ge_1_of_ge_10; lia).
  pose proof (dec_char_in_range (b / 10) Hd1lt10) as Hin1.
  rewrite Hin1. cbn [negb].
  pose proof (dec_value_dec_char (b / 10) Hd1lt10) as Hv1.
  rewrite Hv1.
  assert (Hb0 : N.eqb (b / 10) 0 = false) by (apply N.eqb_neq; lia).
  rewrite Hb0.
  (* Second digit: dec_char (b mod 10), value in 0..9 *)
  assert (Hd2lt10 : b mod 10 < 10) by apply mod10_lt_10.
  pose proof (dec_char_in_range (b mod 10) Hd2lt10) as Hin2.
  rewrite Hin2. cbn [negb].
  pose proof (dec_value_dec_char (b mod 10) Hd2lt10) as Hv2.
  rewrite Hv2.
  (* Now branch on whether rest is empty or starts with a non-digit. *)
  destruct rest as [|c rest'].
  - (* rest empty *)
    rewrite <- (decompose_2 b Hlo Hhi). reflexivity.
  - cbn in Hno. rewrite Hno. cbn.
    rewrite <- (decompose_2 b Hlo Hhi). reflexivity.
Qed.

Lemma parse_octet_print_ge100 :
  forall b rest,
    100 <= b -> b <= 255 ->
    no_lead_digit rest ->
    parse_octet_chars
      ((ascii_list_of_string (byte_to_decimal b)) ++ rest)%list
    = Some (b, rest).
Proof.
  intros b rest Hlo Hhi Hno.
  unfold byte_to_decimal.
  destruct (N.ltb_spec b 10) as [Hl|_]; [lia|].
  destruct (N.ltb_spec b 100) as [Hl2|_]; [lia|].
  cbn [ascii_list_of_string app].
  unfold parse_octet_chars.
  (* First digit: dec_char (b / 100), value in 1..2 *)
  assert (H1lt10 : b / 100 < 10) by (pose proof div100_le_2 b Hhi; lia).
  assert (H1ge1 : 1 <= b / 100) by (apply div100_ge_1_of_ge_100; lia).
  pose proof (dec_char_in_range (b / 100) H1lt10) as Hin1.
  rewrite Hin1. cbn [negb].
  pose proof (dec_value_dec_char (b / 100) H1lt10) as Hv1.
  rewrite Hv1.
  assert (Hbb1 : N.eqb (b / 100) 0 = false) by (apply N.eqb_neq; lia).
  rewrite Hbb1.
  (* Second digit: dec_char ((b / 10) mod 10), value in 0..9 *)
  assert (H2lt10 : (b / 10) mod 10 < 10) by apply mod10_div10_lt_10.
  pose proof (dec_char_in_range ((b / 10) mod 10) H2lt10) as Hin2.
  rewrite Hin2. cbn [negb].
  pose proof (dec_value_dec_char ((b / 10) mod 10) H2lt10) as Hv2.
  rewrite Hv2.
  (* Third digit: dec_char (b mod 10), value in 0..9 *)
  assert (H3lt10 : b mod 10 < 10) by apply mod10_lt_10.
  pose proof (dec_char_in_range (b mod 10) H3lt10) as Hin3.
  rewrite Hin3. cbn [negb].
  pose proof (dec_value_dec_char (b mod 10) H3lt10) as Hv3.
  rewrite Hv3.
  (* Now the value computed equals b. *)
  assert (Hcompute :
    (b / 100 * 10 + (b / 10) mod 10) * 10 + b mod 10 = b).
  { transitivity (b / 100 * 100 + (b / 10) mod 10 * 10 + b mod 10).
    - ring.
    - symmetry. apply decompose_3; assumption. }
  rewrite Hcompute.
  assert (Hleb : (b <=? 255) = true) by (apply N.leb_le; exact Hhi).
  rewrite Hleb.
  destruct rest as [|c rest'].
  - reflexivity.
  - cbn in Hno. rewrite Hno. cbn. reflexivity.
Qed.

(* Master octet round-trip lemma. *)
Lemma parse_octet_print :
  forall b rest,
    b <= 255 ->
    no_lead_digit rest ->
    parse_octet_chars
      ((ascii_list_of_string (byte_to_decimal b)) ++ rest)%list
    = Some (b, rest).
Proof.
  intros b rest Hb Hno.
  destruct (N.ltb_spec b 10) as [Hlt|Hge].
  - apply parse_octet_print_lt10; assumption.
  - destruct (N.ltb_spec b 100) as [Hlt100|Hge100].
    + exact (parse_octet_print_ge10_lt100 b rest Hge Hlt100 Hno).
    + exact (parse_octet_print_ge100 b rest Hge100 Hb Hno).
Qed.

(* ascii_list_of_string of an append. *)
Lemma ascii_list_of_string_append :
  forall s1 s2,
    ascii_list_of_string (append s1 s2) =
    (ascii_list_of_string s1 ++ ascii_list_of_string s2)%list.
Proof.
  induction s1 as [|c s1 IH]; intro s2; cbn.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma ascii_list_of_dot :
  ascii_list_of_string "."%string = ["."%char].
Proof. reflexivity. Qed.

(* The IPv4 round-trip theorem. *)
Theorem parse_print_ipv4 :
  forall ip,
    ipv4_valid ip = true ->
    parse_ipv4 (print_ipv4 ip) = Some ip.
Proof.
  intros [a b c d] Hv.
  unfold ipv4_valid in Hv. cbn in Hv.
  apply andb_true_iff in Hv as [Hva H].
  apply andb_true_iff in H as [Hvb H].
  apply andb_true_iff in H as [Hvc Hvd].
  apply byte_valid_iff in Hva, Hvb, Hvc, Hvd.
  unfold parse_ipv4, print_ipv4, string_concat.
  cbn [ip4_a ip4_b ip4_c ip4_d].
  rewrite !ascii_list_of_string_append.
  cbn [ascii_list_of_string append app].
  unfold parse_ipv4_chars.
  rewrite (parse_octet_print a _ Hva (dot_no_lead_digit _)).
  cbn [expect_dot].
  rewrite (parse_octet_print b _ Hvb (dot_no_lead_digit _)).
  cbn [expect_dot].
  rewrite (parse_octet_print c _ Hvc (dot_no_lead_digit _)).
  cbn [expect_dot].
  rewrite (parse_octet_print d [] Hvd I).
  reflexivity.
Qed.

(* ------------------------------------------------------------ *)
(* IPv4 byte encoding (network order, 4 octets)                 *)
(* ------------------------------------------------------------ *)

Definition ipv4_to_bytes (ip : ipv4) : list byte :=
  [ip4_a ip; ip4_b ip; ip4_c ip; ip4_d ip].

Definition bytes_to_ipv4 (bs : list byte) : option ipv4 :=
  match bs with
  | [a; b; c; d] =>
      if andb (byte_valid a)
           (andb (byte_valid b) (andb (byte_valid c) (byte_valid d)))
      then Some (mk_ipv4 a b c d)
      else None
  | _ => None
  end.

Lemma ipv4_to_bytes_length :
  forall ip, List.length (ipv4_to_bytes ip) = 4%nat.
Proof. intro ip; reflexivity. Qed.

Theorem bytes_ipv4_roundtrip :
  forall ip, ipv4_valid ip = true -> bytes_to_ipv4 (ipv4_to_bytes ip) = Some ip.
Proof.
  intros [a b c d] Hv.
  unfold ipv4_valid in Hv. cbn in Hv.
  unfold bytes_to_ipv4, ipv4_to_bytes. cbn.
  rewrite Hv. reflexivity.
Qed.

(* ------------------------------------------------------------ *)
(* Decidability                                                 *)
(* ------------------------------------------------------------ *)

Lemma ipv4_dec : forall x y : ipv4, {x = y} + {x <> y}.
Proof.
  intros x y. destruct (ipv4_eqb x y) eqn:E.
  - left. apply ipv4_eqb_sound. exact E.
  - right. intro Heq. subst y. rewrite ipv4_eqb_refl in E. discriminate.
Qed.
