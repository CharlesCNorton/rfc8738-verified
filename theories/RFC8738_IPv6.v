(******************************************************************************)
(*                                                                            *)
(*  RFC 8738: IPv6 model                                                      *)
(*                                                                            *)
(*  IPv6 ADT (8 × 16-bit groups), RFC 5952 §4 canonical printer (lowercase    *)
(*  hex, leading-zero suppression, longest-run zero compression with leftmost *)
(*  tie-break, single-zero non-compression), parser handling `::` and hex     *)
(*  digits in either case, IPv4-mapped detection per RFC 8738 §3.             *)
(*                                                                            *)
(******************************************************************************)

From Coq Require Import
  List String Ascii NArith.NArith ZArith Arith Lia Bool.
Require Import RFC8738_Prelude RFC8738_IPv4.

Import ListNotations.
Open Scope N_scope.

(* ------------------------------------------------------------ *)
(* IPv6 ADT (8 × 16-bit groups)                                 *)
(* ------------------------------------------------------------ *)

Record ipv6 := mk_ipv6 {
  ip6_g0 : word16;
  ip6_g1 : word16;
  ip6_g2 : word16;
  ip6_g3 : word16;
  ip6_g4 : word16;
  ip6_g5 : word16;
  ip6_g6 : word16;
  ip6_g7 : word16
}.

Definition ipv6_groups (ip : ipv6) : list word16 :=
  [ip6_g0 ip; ip6_g1 ip; ip6_g2 ip; ip6_g3 ip;
   ip6_g4 ip; ip6_g5 ip; ip6_g6 ip; ip6_g7 ip].

Lemma ipv6_groups_length : forall ip, List.length (ipv6_groups ip) = 8%nat.
Proof. intro ip; reflexivity. Qed.

Definition ipv6_valid (ip : ipv6) : bool :=
  forallb word16_valid (ipv6_groups ip).

Definition ipv6_eqb (x y : ipv6) : bool :=
  list_word16_eqb (ipv6_groups x) (ipv6_groups y).

Lemma ipv6_eqb_refl : forall ip, ipv6_eqb ip ip = true.
Proof. intro ip; unfold ipv6_eqb; apply list_word16_eqb_refl. Qed.

Lemma ipv6_eqb_sound : forall x y, ipv6_eqb x y = true -> x = y.
Proof.
  intros [x0 x1 x2 x3 x4 x5 x6 x7] [y0 y1 y2 y3 y4 y5 y6 y7] H.
  unfold ipv6_eqb in H. cbn in H.
  apply andb_true_iff in H as [H0 H].
  apply andb_true_iff in H as [H1 H].
  apply andb_true_iff in H as [H2 H].
  apply andb_true_iff in H as [H3 H].
  apply andb_true_iff in H as [H4 H].
  apply andb_true_iff in H as [H5 H].
  apply andb_true_iff in H as [H6 H].
  apply andb_true_iff in H as [H7 _].
  apply word16_eqb_sound in H0, H1, H2, H3, H4, H5, H6, H7.
  subst. reflexivity.
Qed.

(* Reconstruct an IPv6 record from a list of exactly 8 groups. *)
Definition ipv6_from_groups (gs : list word16) : option ipv6 :=
  match gs with
  | [g0; g1; g2; g3; g4; g5; g6; g7] => Some (mk_ipv6 g0 g1 g2 g3 g4 g5 g6 g7)
  | _ => None
  end.

Lemma ipv6_from_groups_inv :
  forall ip, ipv6_from_groups (ipv6_groups ip) = Some ip.
Proof. intros [g0 g1 g2 g3 g4 g5 g6 g7]; reflexivity. Qed.

(* ------------------------------------------------------------ *)
(* IPv4-mapped IPv6 (RFC 4291 §2.5.5.2 / RFC 8738 §3 rejection) *)
(* ------------------------------------------------------------ *)

(* IPv4-mapped form: ::ffff:a.b.c.d, i.e., groups [0;0;0;0;0;ffff;hi;lo]. *)
Definition is_ipv4_mapped (ip : ipv6) : bool :=
  andb (N.eqb (ip6_g0 ip) 0)
    (andb (N.eqb (ip6_g1 ip) 0)
      (andb (N.eqb (ip6_g2 ip) 0)
        (andb (N.eqb (ip6_g3 ip) 0)
          (andb (N.eqb (ip6_g4 ip) 0)
                (N.eqb (ip6_g5 ip) 0xFFFF))))).

Lemma is_ipv4_mapped_iff :
  forall ip,
    is_ipv4_mapped ip = true <->
    ip6_g0 ip = 0 /\ ip6_g1 ip = 0 /\ ip6_g2 ip = 0 /\
    ip6_g3 ip = 0 /\ ip6_g4 ip = 0 /\ ip6_g5 ip = 0xFFFF.
Proof.
  intro ip. unfold is_ipv4_mapped.
  split.
  - intro H.
    apply andb_true_iff in H as [H0 H].
    apply andb_true_iff in H as [H1 H].
    apply andb_true_iff in H as [H2 H].
    apply andb_true_iff in H as [H3 H].
    apply andb_true_iff in H as [H4 H5].
    apply N.eqb_eq in H0, H1, H2, H3, H4, H5.
    repeat split; assumption.
  - intros [H0 [H1 [H2 [H3 [H4 H5]]]]].
    rewrite H0, H1, H2, H3, H4, H5.
    rewrite !N.eqb_refl. reflexivity.
Qed.

(* ------------------------------------------------------------ *)
(* Zero-run analysis for RFC 5952 §4.2 longest-run compression  *)
(* ------------------------------------------------------------ *)

(* Find all maximal runs of zero groups.  Each run is (start_index, length). *)
Fixpoint zero_runs_aux
    (gs : list word16) (idx cur_start cur_len : nat) : list (nat * nat) :=
  match gs with
  | [] => if Nat.ltb 0 cur_len then [(cur_start, cur_len)] else []
  | g :: gs' =>
      if N.eqb g 0 then
        let new_start := if Nat.eqb cur_len 0 then idx else cur_start in
        zero_runs_aux gs' (S idx) new_start (S cur_len)
      else
        let so_far := if Nat.ltb 0 cur_len then [(cur_start, cur_len)] else [] in
        so_far ++ zero_runs_aux gs' (S idx) 0 0
  end.

Definition zero_runs (gs : list word16) : list (nat * nat) :=
  zero_runs_aux gs 0%nat 0%nat 0%nat.

(* Pick the longest run with leftmost tie-break.  Only consider runs of
   length >= 2 (RFC 5952 §4.2.2: a single zero group must not be compressed). *)
Definition longest_run_pick (runs : list (nat * nat)) : option (nat * nat) :=
  fold_left
    (fun acc r =>
       let '(_, len) := r in
       if Nat.ltb 1 len then
         match acc with
         | None => Some r
         | Some (_, best_len) =>
             if Nat.ltb best_len len then Some r else acc
         end
       else acc)
    runs None.

Definition longest_zero_run (gs : list word16) : option (nat * nat) :=
  longest_run_pick (zero_runs gs).

(* ------------------------------------------------------------ *)
(* Canonical RFC 5952 IPv6 printer                              *)
(* ------------------------------------------------------------ *)

Definition print_groups (gs : list word16) : string :=
  string_intercalate ":"%string (map word16_to_hex_lower gs).

Definition print_ipv6_groups (gs : list word16) : string :=
  match longest_zero_run gs with
  | None => print_groups gs
  | Some (start, len) =>
      let before := List.firstn start gs in
      let after := List.skipn (start + len)%nat gs in
      string_concat
        [print_groups before;
         "::"%string;
         print_groups after]
  end.

Definition print_ipv6 (ip : ipv6) : string :=
  print_ipv6_groups (ipv6_groups ip).

(* ------------------------------------------------------------ *)
(* IPv6 parser                                                  *)
(* ------------------------------------------------------------ *)

(* Tokenize on ":" and "::". *)
Inductive ipv6_tok :=
| TokGroup (w : word16)
| TokDoubleColon.

(* Parse 1-4 hex digits into a word16.  Returns the value and the remaining
   characters.  Fails if the first char is not a hex digit, or if there are
   more than 4 hex digits. *)
Definition parse_hex_group (cs : list ascii) : option (word16 * list ascii) :=
  match cs with
  | [] => None
  | c0 :: r0 =>
      if negb (is_hex_digit c0) then None
      else
        let v0 := hex_value c0 in
        match r0 with
        | [] => Some (v0, [])
        | c1 :: r1 =>
            if negb (is_hex_digit c1) then Some (v0, r0)
            else
              let v1 := v0 * 16 + hex_value c1 in
              match r1 with
              | [] => Some (v1, [])
              | c2 :: r2 =>
                  if negb (is_hex_digit c2) then Some (v1, r1)
                  else
                    let v2 := v1 * 16 + hex_value c2 in
                    match r2 with
                    | [] => Some (v2, [])
                    | c3 :: r3 =>
                        if negb (is_hex_digit c3) then Some (v2, r2)
                        else
                          let v3 := v2 * 16 + hex_value c3 in
                          match r3 with
                          | [] => Some (v3, [])
                          | c4 :: _ =>
                              if is_hex_digit c4 then None  (* > 4 hex *)
                              else Some (v3, r3)
                          end
                    end
              end
        end
  end.

(* Tokenize the IPv6 input.  Returns Some(tokens, dc_position) where
   dc_position is the index of the "::" token if present, or None. *)
Fixpoint tokenize_ipv6_aux
    (fuel : nat) (cs : list ascii) : option (list ipv6_tok) :=
  match fuel with
  | O => None
  | S fuel' =>
      match cs with
      | [] => Some []
      | ":"%char :: ":"%char :: rest =>
          match tokenize_ipv6_aux fuel' rest with
          | None => None
          | Some toks => Some (TokDoubleColon :: toks)
          end
      | ":"%char :: rest =>
          match tokenize_ipv6_aux fuel' rest with
          | None => None
          | Some toks => Some toks  (* drop single colons (separators) *)
          end
      | _ =>
          match parse_hex_group cs with
          | None => None
          | Some (w, rest) =>
              match tokenize_ipv6_aux fuel' rest with
              | None => None
              | Some toks => Some (TokGroup w :: toks)
              end
          end
      end
  end.

Definition tokenize_ipv6 (cs : list ascii) : option (list ipv6_tok) :=
  tokenize_ipv6_aux (S (List.length cs)) cs.

(* Extract groups from token list.  Splits at "::" if present. *)
Fixpoint split_at_double_colon
    (toks : list ipv6_tok) : list word16 * option (list word16) :=
  match toks with
  | [] => ([], None)
  | TokDoubleColon :: rest =>
      ([], Some (filter_map_groups rest))
  | TokGroup w :: rest =>
      let '(before, after) := split_at_double_colon rest in
      (w :: before, after)
  end
with filter_map_groups (toks : list ipv6_tok) : list word16 :=
  match toks with
  | [] => []
  | TokGroup w :: rest => w :: filter_map_groups rest
  | TokDoubleColon :: rest => filter_map_groups rest  (* defensive: ignore *)
  end.

(* Reconstruct 8-group IPv6 from before/after lists.  Pads zeros at the
   double-colon position. *)
Definition reconstruct_ipv6
    (before : list word16) (after_opt : option (list word16))
    : option (list word16) :=
  let nb := List.length before in
  match after_opt with
  | None =>
      (* No "::" — must have exactly 8 groups. *)
      if Nat.eqb nb 8 then Some before else None
  | Some after =>
      let na := List.length after in
      if Nat.leb (nb + na) 7 then
        Some (before ++ List.repeat 0 (8 - nb - na) ++ after)
      else
        None
  end.

Definition parse_ipv6_chars (cs : list ascii) : option ipv6 :=
  match tokenize_ipv6 cs with
  | None => None
  | Some toks =>
      let '(before, after_opt) := split_at_double_colon toks in
      match reconstruct_ipv6 before after_opt with
      | None => None
      | Some gs => ipv6_from_groups gs
      end
  end.

Definition parse_ipv6 (s : string) : option ipv6 :=
  parse_ipv6_chars (ascii_list_of_string s).

(* ------------------------------------------------------------ *)
(* Specific RFC 5952 examples (vm_compute regression tests)     *)
(* ------------------------------------------------------------ *)

Example print_unspecified :
  print_ipv6 (mk_ipv6 0 0 0 0 0 0 0 0) = "::"%string.
Proof. vm_compute. reflexivity. Qed.

Example print_loopback :
  print_ipv6 (mk_ipv6 0 0 0 0 0 0 0 1) = "::1"%string.
Proof. vm_compute. reflexivity. Qed.

Example print_documentation :
  print_ipv6 (mk_ipv6 0x2001 0xdb8 0 0 0 0 0 1) = "2001:db8::1"%string.
Proof. vm_compute. reflexivity. Qed.

Example print_no_compression :
  print_ipv6 (mk_ipv6 0xfe80 1 2 3 4 5 6 7) = "fe80:1:2:3:4:5:6:7"%string.
Proof. vm_compute. reflexivity. Qed.

Example print_leftmost_run :
  (* Two equal-length runs: pick leftmost.
     [1;0;0;1;0;0;1;1] -> "1::1:0:0:1:1" (compress positions 1-2). *)
  print_ipv6 (mk_ipv6 1 0 0 1 0 0 1 1) = "1::1:0:0:1:1"%string.
Proof. vm_compute. reflexivity. Qed.

Example print_no_single_zero_compression :
  (* Single zero must NOT be compressed (RFC 5952 §4.2.2). *)
  print_ipv6 (mk_ipv6 1 0 1 1 1 1 1 1) = "1:0:1:1:1:1:1:1"%string.
Proof. vm_compute. reflexivity. Qed.

Example parse_unspecified :
  parse_ipv6 "::" = Some (mk_ipv6 0 0 0 0 0 0 0 0).
Proof. vm_compute. reflexivity. Qed.

Example parse_loopback :
  parse_ipv6 "::1" = Some (mk_ipv6 0 0 0 0 0 0 0 1).
Proof. vm_compute. reflexivity. Qed.

Example parse_documentation :
  parse_ipv6 "2001:db8::1" = Some (mk_ipv6 0x2001 0xdb8 0 0 0 0 0 1).
Proof. vm_compute. reflexivity. Qed.

Example parse_full :
  parse_ipv6 "fe80:1:2:3:4:5:6:7"
  = Some (mk_ipv6 0xfe80 1 2 3 4 5 6 7).
Proof. vm_compute. reflexivity. Qed.

Example parse_uppercase_accepted :
  parse_ipv6 "2001:DB8::1" = Some (mk_ipv6 0x2001 0xdb8 0 0 0 0 0 1).
Proof. vm_compute. reflexivity. Qed.

Example parse_leading_zeros_accepted :
  parse_ipv6 "2001:0db8::0001" = Some (mk_ipv6 0x2001 0xdb8 0 0 0 0 0 1).
Proof. vm_compute. reflexivity. Qed.

Example parse_print_unspecified :
  parse_ipv6 (print_ipv6 (mk_ipv6 0 0 0 0 0 0 0 0))
  = Some (mk_ipv6 0 0 0 0 0 0 0 0).
Proof. vm_compute. reflexivity. Qed.

Example parse_print_loopback :
  parse_ipv6 (print_ipv6 (mk_ipv6 0 0 0 0 0 0 0 1))
  = Some (mk_ipv6 0 0 0 0 0 0 0 1).
Proof. vm_compute. reflexivity. Qed.

Example parse_print_documentation :
  parse_ipv6 (print_ipv6 (mk_ipv6 0x2001 0xdb8 0 0 0 0 0 1))
  = Some (mk_ipv6 0x2001 0xdb8 0 0 0 0 0 1).
Proof. vm_compute. reflexivity. Qed.

Example parse_print_no_compression :
  parse_ipv6 (print_ipv6 (mk_ipv6 0xfe80 1 2 3 4 5 6 7))
  = Some (mk_ipv6 0xfe80 1 2 3 4 5 6 7).
Proof. vm_compute. reflexivity. Qed.

(* RFC 8738 §3: IPv4-mapped form is rejected for IP identifier use. *)
Example ipv4_mapped_detected :
  is_ipv4_mapped (mk_ipv6 0 0 0 0 0 0xFFFF 0xC000 0x0201) = true.
Proof. reflexivity. Qed.

Example ipv4_mapped_rejected_for_typical_global :
  is_ipv4_mapped (mk_ipv6 0x2001 0xdb8 0 0 0 0 0 1) = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------ *)
(* IPv6 byte encoding (16 bytes, big-endian)                    *)
(* ------------------------------------------------------------ *)

Definition word16_to_bytes (w : word16) : list byte :=
  [w / 256; w mod 256].

Definition bytes_to_word16 (hi lo : byte) : word16 :=
  hi * 256 + lo.

Lemma word16_to_bytes_inv :
  forall w, w <= word16_max ->
    let bs := word16_to_bytes w in
    bytes_to_word16 (List.nth 0 bs 0) (List.nth 1 bs 0) = w.
Proof.
  intros w Hw. cbn.
  unfold bytes_to_word16.
  rewrite (N.div_mod w 256) at 3 by lia. lia.
Qed.

Definition ipv6_to_bytes (ip : ipv6) : list byte :=
  List.concat (List.map word16_to_bytes (ipv6_groups ip)).

Lemma ipv6_to_bytes_length : forall ip, List.length (ipv6_to_bytes ip) = 16%nat.
Proof. intros [g0 g1 g2 g3 g4 g5 g6 g7]; reflexivity. Qed.

(* ------------------------------------------------------------ *)
(* Decidability                                                 *)
(* ------------------------------------------------------------ *)

Lemma ipv6_dec : forall x y : ipv6, {x = y} + {x <> y}.
Proof.
  intros x y. destruct (ipv6_eqb x y) eqn:E.
  - left. apply ipv6_eqb_sound. exact E.
  - right. intro Heq. subst y. rewrite ipv6_eqb_refl in E. discriminate.
Qed.
