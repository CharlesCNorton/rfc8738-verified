(******************************************************************************)
(*                                                                            *)
(*  RFC 8738: ACME Identifier wrapper for IP addresses                        *)
(*                                                                            *)
(*  ip_address sum type (IPv4 / IPv6), ACME identifier record per             *)
(*  RFC 8555 §7.1.4 with type "ip", parse pipeline including the              *)
(*  RFC 8738 §3 rejection of IPv4-mapped IPv6 addresses.                      *)
(*                                                                            *)
(******************************************************************************)

From Coq Require Import
  List String Ascii NArith.NArith ZArith Arith Lia Bool.
Require Import RFC8738_Prelude RFC8738_IPv4 RFC8738_IPv6.

Import ListNotations.
Open Scope N_scope.

(* ------------------------------------------------------------ *)
(* The IP address sum type                                      *)
(* ------------------------------------------------------------ *)

Inductive ip_address :=
| IPAddrV4 (ip : ipv4)
| IPAddrV6 (ip : ipv6).

Definition ip_address_valid (ip : ip_address) : bool :=
  match ip with
  | IPAddrV4 v => ipv4_valid v
  | IPAddrV6 v => ipv6_valid v
  end.

Definition ip_address_eqb (x y : ip_address) : bool :=
  match x, y with
  | IPAddrV4 a, IPAddrV4 b => ipv4_eqb a b
  | IPAddrV6 a, IPAddrV6 b => ipv6_eqb a b
  | _, _ => false
  end.

Lemma ip_address_eqb_refl : forall ip, ip_address_eqb ip ip = true.
Proof.
  intros [v|v]; simpl.
  - apply ipv4_eqb_refl.
  - apply ipv6_eqb_refl.
Qed.

Lemma ip_address_eqb_sound :
  forall x y, ip_address_eqb x y = true -> x = y.
Proof.
  intros [a|a] [b|b] H; simpl in H; try discriminate.
  - f_equal. apply ipv4_eqb_sound; exact H.
  - f_equal. apply ipv6_eqb_sound; exact H.
Qed.

(* ------------------------------------------------------------ *)
(* Print / parse with explicit IPv4-vs-IPv6 discrimination      *)
(* ------------------------------------------------------------ *)

Definition print_ip (ip : ip_address) : string :=
  match ip with
  | IPAddrV4 v => print_ipv4 v
  | IPAddrV6 v => print_ipv6 v
  end.

(* Test whether an ASCII char list contains a given character. *)
Fixpoint chars_contain (cs : list ascii) (target : ascii) : bool :=
  match cs with
  | [] => false
  | c :: rest => orb (Ascii.eqb c target) (chars_contain rest target)
  end.

Definition string_contains_char (s : string) (c : ascii) : bool :=
  chars_contain (ascii_list_of_string s) c.

(* Discriminate IPv4 vs IPv6 by looking for ':'.  IPv6 literals always
   contain at least one colon (even the unspecified address "::"),
   while IPv4 dotted-decimal contains none. *)
Definition parse_ip (s : string) : option ip_address :=
  if string_contains_char s ":"%char then
    match parse_ipv6 s with
    | Some v => Some (IPAddrV6 v)
    | None => None
    end
  else
    match parse_ipv4 s with
    | Some v => Some (IPAddrV4 v)
    | None => None
    end.

(* ------------------------------------------------------------ *)
(* RFC 8738 §3: reject IPv4-mapped IPv6 for the "ip" identifier *)
(* ------------------------------------------------------------ *)

Definition ip_address_acceptable (ip : ip_address) : bool :=
  match ip with
  | IPAddrV4 _ => true
  | IPAddrV6 v => negb (is_ipv4_mapped v)
  end.

Definition ip_address_acme_ok (ip : ip_address) : bool :=
  andb (ip_address_valid ip) (ip_address_acceptable ip).

Lemma ip_address_acme_ok_iff :
  forall ip,
    ip_address_acme_ok ip = true <->
    ip_address_valid ip = true /\ ip_address_acceptable ip = true.
Proof.
  intro ip. unfold ip_address_acme_ok. apply andb_true_iff.
Qed.

Theorem ipv4_mapped_v6_rejected :
  forall v,
    is_ipv4_mapped v = true ->
    ip_address_acceptable (IPAddrV6 v) = false.
Proof.
  intros v H. simpl. rewrite H. reflexivity.
Qed.

Theorem ipv4_address_always_acceptable :
  forall v, ip_address_acceptable (IPAddrV4 v) = true.
Proof. intros v; reflexivity. Qed.

(* ------------------------------------------------------------ *)
(* ACME identifier (RFC 8555 §7.1.4 surface)                    *)
(* ------------------------------------------------------------ *)

Record acme_identifier := {
  aid_type  : string;   (* "ip" for RFC 8738; "dns" for RFC 8555 default *)
  aid_value : string    (* IP literal text *)
}.

Definition acme_id_type_ip : string := "ip"%string.

Definition is_ip_identifier (aid : acme_identifier) : bool :=
  string_eqb (aid_type aid) acme_id_type_ip.

(* Parse an ACME identifier of type "ip" into an ip_address.  Rejects:
   - identifiers whose type is not "ip"
   - values that fail IP address parsing
   - IPv4-mapped IPv6 values per RFC 8738 §3 *)
Inductive id_parse_error :=
| IPE_WrongType         (* aid_type != "ip" *)
| IPE_MalformedValue    (* parse_ip returned None *)
| IPE_IPv4MappedV6.     (* RFC 8738 §3 forbids ::ffff:a.b.c.d *)

Definition parse_ip_identifier
    (aid : acme_identifier) : id_parse_error + ip_address :=
  if negb (is_ip_identifier aid) then inl IPE_WrongType
  else
    match parse_ip (aid_value aid) with
    | None => inl IPE_MalformedValue
    | Some ip =>
        if ip_address_acceptable ip then inr ip
        else inl IPE_IPv4MappedV6
    end.

Theorem parse_ip_identifier_wrong_type :
  forall aid,
    is_ip_identifier aid = false ->
    parse_ip_identifier aid = inl IPE_WrongType.
Proof.
  intros aid H. unfold parse_ip_identifier.
  rewrite H. reflexivity.
Qed.

Theorem parse_ip_identifier_malformed :
  forall aid,
    is_ip_identifier aid = true ->
    parse_ip (aid_value aid) = None ->
    parse_ip_identifier aid = inl IPE_MalformedValue.
Proof.
  intros aid Ht Hp. unfold parse_ip_identifier.
  rewrite Ht. cbn. rewrite Hp. reflexivity.
Qed.

Theorem parse_ip_identifier_ipv4_mapped_rejected :
  forall aid v,
    is_ip_identifier aid = true ->
    parse_ip (aid_value aid) = Some (IPAddrV6 v) ->
    is_ipv4_mapped v = true ->
    parse_ip_identifier aid = inl IPE_IPv4MappedV6.
Proof.
  intros aid v Ht Hp Hm. unfold parse_ip_identifier.
  rewrite Ht. cbn. rewrite Hp.
  cbn. rewrite Hm. reflexivity.
Qed.

Theorem parse_ip_identifier_ok :
  forall aid ip,
    is_ip_identifier aid = true ->
    parse_ip (aid_value aid) = Some ip ->
    ip_address_acceptable ip = true ->
    parse_ip_identifier aid = inr ip.
Proof.
  intros aid ip Ht Hp Ha. unfold parse_ip_identifier.
  rewrite Ht. cbn. rewrite Hp, Ha. reflexivity.
Qed.

(* Constructor: build an ACME identifier from an IP address. *)
Definition build_ip_identifier (ip : ip_address) : acme_identifier :=
  {| aid_type := acme_id_type_ip;
     aid_value := print_ip ip |}.

Lemma build_ip_identifier_type :
  forall ip, is_ip_identifier (build_ip_identifier ip) = true.
Proof.
  intro ip. unfold is_ip_identifier, build_ip_identifier. simpl.
  apply string_eqb_refl.
Qed.

(* ------------------------------------------------------------ *)
(* IPv4 round-trip through the discriminating parser            *)
(* ------------------------------------------------------------ *)

(* dec_char produces digits in '0'..'9' (ASCII 48-57), never ':' (ASCII 58). *)
Lemma dec_char_not_colon :
  forall n, n < 10 -> Ascii.eqb (dec_char n) ":"%char = false.
Proof.
  intros n Hn.
  destruct (Ascii.eqb (dec_char n) ":"%char) eqn:E; [|reflexivity].
  exfalso.
  apply Ascii.eqb_eq in E.
  apply (f_equal nat_of_ascii) in E.
  unfold dec_char, N_to_ascii in E.
  assert (Hbound : (N.to_nat (n + 48) < 256)%nat).
  { pose proof (N_lt_to_nat (n + 48) 256) as HH. cbn in HH. apply HH. lia. }
  rewrite (nat_ascii_embedding _ Hbound) in E.
  cbn in E. lia.
Qed.

(* The IPv4 dotted-decimal text contains no colon (for valid bytes). *)
Lemma byte_to_decimal_no_colon :
  forall b, b <= 255 ->
    chars_contain (ascii_list_of_string (byte_to_decimal b)) ":"%char = false.
Proof.
  intros b Hb. unfold byte_to_decimal.
  destruct (N.ltb_spec b 10) as [Hlt|Hge].
  - cbn. rewrite dec_char_not_colon by exact Hlt. reflexivity.
  - destruct (N.ltb_spec b 100) as [Hlt100|Hge100].
    + cbn.
      rewrite dec_char_not_colon by (apply div10_lt_10; lia).
      cbn.
      rewrite dec_char_not_colon by apply mod10_lt_10.
      reflexivity.
    + cbn.
      assert (Hd100 : b / 100 < 10).
      { enough (b / 100 < 3) by lia. apply N.Div0.div_lt_upper_bound. lia. }
      rewrite dec_char_not_colon by exact Hd100.
      cbn.
      rewrite dec_char_not_colon by apply mod10_div10_lt_10.
      cbn.
      rewrite dec_char_not_colon by apply mod10_lt_10.
      reflexivity.
Qed.

Lemma chars_contain_app :
  forall xs ys c,
    chars_contain (xs ++ ys) c = orb (chars_contain xs c) (chars_contain ys c).
Proof.
  induction xs as [|x xs IH]; intros ys c; cbn.
  - reflexivity.
  - rewrite IH. rewrite Bool.orb_assoc. reflexivity.
Qed.

Lemma chars_contain_dot_neq_colon :
  chars_contain ["."%char] ":"%char = false.
Proof. reflexivity. Qed.

Lemma print_ipv4_no_colon :
  forall v,
    ipv4_valid v = true ->
    string_contains_char (print_ipv4 v) ":"%char = false.
Proof.
  intros [a b c d] Hv.
  unfold ipv4_valid in Hv. cbn in Hv.
  apply andb_true_iff in Hv as [Hva H].
  apply andb_true_iff in H as [Hvb H].
  apply andb_true_iff in H as [Hvc Hvd].
  apply byte_valid_iff in Hva, Hvb, Hvc, Hvd.
  unfold string_contains_char, print_ipv4, string_concat.
  cbn [ip4_a ip4_b ip4_c ip4_d].
  rewrite !ascii_list_of_string_append.
  rewrite !chars_contain_app.
  rewrite (byte_to_decimal_no_colon a Hva),
          (byte_to_decimal_no_colon b Hvb),
          (byte_to_decimal_no_colon c Hvc),
          (byte_to_decimal_no_colon d Hvd).
  cbn. reflexivity.
Qed.

Theorem print_parse_ipv4_round_trip :
  forall v,
    ipv4_valid v = true ->
    parse_ip (print_ip (IPAddrV4 v)) = Some (IPAddrV4 v).
Proof.
  intros v Hv. unfold print_ip, parse_ip.
  rewrite (print_ipv4_no_colon v Hv).
  rewrite (parse_print_ipv4 v Hv). reflexivity.
Qed.

(* ------------------------------------------------------------ *)
(* Decidability                                                 *)
(* ------------------------------------------------------------ *)

Lemma ip_address_dec : forall x y : ip_address, {x = y} + {x <> y}.
Proof.
  intros x y. destruct (ip_address_eqb x y) eqn:E.
  - left. apply ip_address_eqb_sound. exact E.
  - right. intro Heq. subst y. rewrite ip_address_eqb_refl in E. discriminate.
Qed.
