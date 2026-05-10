(******************************************************************************)
(*                                                                            *)
(*  RFC 8738: ACME IP Identifier Validation Extension                         *)
(*  Prelude: numeric types, digit predicates, string helpers                  *)
(*                                                                            *)
(******************************************************************************)

From Coq Require Import
  List String Ascii NArith.NArith ZArith Arith Lia Bool.

Import ListNotations.
Open Scope N_scope.

(* ------------------------------------------------------------ *)
(* Numeric type aliases                                         *)
(* ------------------------------------------------------------ *)

Definition byte   := N.   (* [0, 255]   *)
Definition word16 := N.   (* [0, 65535] *)
Definition word32 := N.   (* [0, 2^32)  *)

Definition byte_max   : N := 255.
Definition word16_max : N := 65535.

Definition byte_valid (b : N) : bool := N.leb b byte_max.
Definition word16_valid (w : N) : bool := N.leb w word16_max.

Lemma byte_valid_iff : forall b, byte_valid b = true <-> b <= byte_max.
Proof. intro b; unfold byte_valid; apply N.leb_le. Qed.

Lemma word16_valid_iff : forall w, word16_valid w = true <-> w <= word16_max.
Proof. intro w; unfold word16_valid; apply N.leb_le. Qed.

(* ------------------------------------------------------------ *)
(* N <-> nat lt bridge (the stdlib is missing inj_lt here)      *)
(* ------------------------------------------------------------ *)

Lemma N_lt_to_nat :
  forall n m, n < m -> (N.to_nat n < N.to_nat m)%nat.
Proof.
  intros n m Hlt.
  apply N.compare_lt_iff in Hlt.
  rewrite N2Nat.inj_compare in Hlt.
  apply Nat.compare_lt_iff in Hlt.
  exact Hlt.
Qed.

Lemma N_of_nat_lt :
  forall (n m : nat), (n < m)%nat -> N.of_nat n < N.of_nat m.
Proof. intros n m Hlt. lia. Qed.

(* ------------------------------------------------------------ *)
(* ASCII <-> N round-trip                                       *)
(* ------------------------------------------------------------ *)

Definition ascii_to_N (c : ascii) : N := N.of_nat (nat_of_ascii c).

Definition N_to_ascii (n : N) : ascii := ascii_of_nat (N.to_nat n).

Lemma ascii_N_roundtrip :
  forall n, n < 256 -> ascii_to_N (N_to_ascii n) = n.
Proof.
  intros n Hlt.
  unfold ascii_to_N, N_to_ascii.
  assert (Hb : (N.to_nat n < 256)%nat).
  { pose proof (N_lt_to_nat n 256 Hlt) as H. cbn in H. exact H. }
  rewrite (nat_ascii_embedding (N.to_nat n) Hb).
  rewrite N2Nat.id. reflexivity.
Qed.

Lemma ascii_to_N_bounded :
  forall c, ascii_to_N c < 256.
Proof.
  intro c. unfold ascii_to_N.
  pose proof (nat_ascii_bounded c) as Hb.
  pose proof (N_of_nat_lt (nat_of_ascii c) 256 Hb) as H.
  cbn in H. exact H.
Qed.

(* ------------------------------------------------------------ *)
(* Decimal digits                                               *)
(* ------------------------------------------------------------ *)

Definition is_dec_digit (c : ascii) : bool :=
  let n := ascii_to_N c in
  andb (N.leb 48 n) (N.leb n 57).

Definition dec_value (c : ascii) : N :=
  let n := ascii_to_N c in
  if andb (N.leb 48 n) (N.leb n 57) then n - 48 else 0.

Definition dec_char (n : N) : ascii := N_to_ascii (n + 48).

Lemma dec_char_in_range :
  forall n, n < 10 -> is_dec_digit (dec_char n) = true.
Proof.
  intros n Hlt. unfold is_dec_digit, dec_char.
  assert (H : ascii_to_N (N_to_ascii (n + 48)) = n + 48).
  { apply ascii_N_roundtrip. lia. }
  rewrite H.
  apply andb_true_iff. split; apply N.leb_le; lia.
Qed.

Lemma dec_value_dec_char :
  forall n, n < 10 -> dec_value (dec_char n) = n.
Proof.
  intros n Hlt. unfold dec_value, dec_char.
  assert (H : ascii_to_N (N_to_ascii (n + 48)) = n + 48).
  { apply ascii_N_roundtrip. lia. }
  rewrite H.
  assert (Hl : (48 <=? n + 48) = true) by (apply N.leb_le; lia).
  assert (Hh : (n + 48 <=? 57) = true) by (apply N.leb_le; lia).
  rewrite Hl, Hh. cbn. lia.
Qed.

Lemma dec_value_lt_10 :
  forall c, is_dec_digit c = true -> dec_value c < 10.
Proof.
  intros c H. unfold is_dec_digit, dec_value in *.
  rewrite H. apply andb_true_iff in H as [Hl Hh].
  apply N.leb_le in Hl. apply N.leb_le in Hh. lia.
Qed.

(* ------------------------------------------------------------ *)
(* Hex digits (lowercase canonical for RFC 5952)                *)
(* ------------------------------------------------------------ *)

Definition is_hex_digit (c : ascii) : bool :=
  let n := ascii_to_N c in
  orb (andb (N.leb 48 n) (N.leb n 57))                       (* 0..9 *)
      (orb (andb (N.leb 65 n) (N.leb n 70))                  (* A..F *)
           (andb (N.leb 97 n) (N.leb n 102))).               (* a..f *)

Definition hex_value (c : ascii) : N :=
  let n := ascii_to_N c in
  if andb (N.leb 48 n) (N.leb n 57) then n - 48
  else if andb (N.leb 65 n) (N.leb n 70) then n - 65 + 10
  else if andb (N.leb 97 n) (N.leb n 102) then n - 97 + 10
  else 0.

(* Canonical lowercase hex character. *)
Definition hex_char (n : N) : ascii :=
  if N.ltb n 10
  then N_to_ascii (n + 48)
  else N_to_ascii (n - 10 + 97).

Lemma hex_char_is_hex :
  forall n, n < 16 -> is_hex_digit (hex_char n) = true.
Proof.
  intros n Hlt. unfold is_hex_digit, hex_char.
  destruct (N.ltb_spec n 10) as [Hlo|Hhi].
  - assert (H : ascii_to_N (N_to_ascii (n + 48)) = n + 48)
      by (apply ascii_N_roundtrip; lia).
    rewrite H.
    assert (Hl : (48 <=? n + 48) = true) by (apply N.leb_le; lia).
    assert (Hh : (n + 48 <=? 57) = true) by (apply N.leb_le; lia).
    rewrite Hl, Hh. reflexivity.
  - assert (H : ascii_to_N (N_to_ascii (n - 10 + 97)) = n - 10 + 97)
      by (apply ascii_N_roundtrip; lia).
    rewrite H.
    assert (Hl : (97 <=? n - 10 + 97) = true) by (apply N.leb_le; lia).
    assert (Hh : (n - 10 + 97 <=? 102) = true) by (apply N.leb_le; lia).
    rewrite Hl, Hh.
    rewrite Bool.orb_true_r, Bool.orb_true_r. reflexivity.
Qed.

Lemma hex_value_hex_char :
  forall n, n < 16 -> hex_value (hex_char n) = n.
Proof.
  intros n Hlt. unfold hex_value, hex_char.
  destruct (N.ltb_spec n 10) as [Hlo|Hhi].
  - (* n < 10 -> '0'..'9' branch *)
    assert (H : ascii_to_N (N_to_ascii (n + 48)) = n + 48)
      by (apply ascii_N_roundtrip; lia).
    rewrite H.
    assert (Hl : (48 <=? n + 48) = true) by (apply N.leb_le; lia).
    assert (Hh : (n + 48 <=? 57) = true) by (apply N.leb_le; lia).
    rewrite Hl, Hh. cbn. lia.
  - (* n >= 10 -> 'a'..'f' branch *)
    assert (H : ascii_to_N (N_to_ascii (n - 10 + 97)) = n - 10 + 97)
      by (apply ascii_N_roundtrip; lia).
    rewrite H.
    (* digit branch fails: char value in [97,102] > 57 *)
    assert (Hd : (n - 10 + 97 <=? 57) = false) by (apply N.leb_gt; lia).
    rewrite Hd, Bool.andb_false_r. cbn.
    (* uppercase branch fails: char value in [97,102] > 70 *)
    assert (Hu : (n - 10 + 97 <=? 70) = false) by (apply N.leb_gt; lia).
    rewrite Hu, Bool.andb_false_r. cbn.
    (* lowercase branch succeeds *)
    assert (Hll : (97 <=? n - 10 + 97) = true) by (apply N.leb_le; lia).
    assert (Hlh : (n - 10 + 97 <=? 102) = true) by (apply N.leb_le; lia).
    rewrite Hll, Hlh. cbn. lia.
Qed.

Lemma hex_value_lt_16 :
  forall c, is_hex_digit c = true -> hex_value c < 16.
Proof.
  intros c H. unfold is_hex_digit, hex_value in *.
  set (n := ascii_to_N c) in *.
  destruct (andb (48 <=? n) (n <=? 57)) eqn:Hd.
  - apply andb_true_iff in Hd as [Hl Hh].
    apply N.leb_le in Hl. apply N.leb_le in Hh. lia.
  - simpl in H.
    destruct (andb (65 <=? n) (n <=? 70)) eqn:Hu.
    + apply andb_true_iff in Hu as [Hl Hh].
      apply N.leb_le in Hl. apply N.leb_le in Hh. lia.
    + simpl in H.
      destruct (andb (97 <=? n) (n <=? 102)) eqn:Hll.
      * apply andb_true_iff in Hll as [Hl Hh].
        apply N.leb_le in Hl. apply N.leb_le in Hh. lia.
      * discriminate.
Qed.

(* ------------------------------------------------------------ *)
(* Bounded byte/word16 case analysis (for stronger lemmas)      *)
(* ------------------------------------------------------------ *)

Lemma byte_pos_to_byte :
  forall b, b <= byte_max -> (N.to_nat b < 256)%nat.
Proof.
  intros b Hb. unfold byte_max in *.
  pose proof (N_lt_to_nat b 256) as H.
  cbn in H. apply H. lia.
Qed.

(* ------------------------------------------------------------ *)
(* Byte -> 3-digit decimal (with leading zeros)                 *)
(* ------------------------------------------------------------ *)

Definition byte_to_digits3 (b : byte) : ascii * ascii * ascii :=
  let h := b / 100 in
  let t := (b / 10) mod 10 in
  let u := b mod 10 in
  (dec_char h, dec_char t, dec_char u).

(* Byte -> shortest decimal (no leading zeros, RFC 1123 §2.1).  *)
Definition byte_to_decimal (b : byte) : string :=
  if N.ltb b 10 then String (dec_char b) EmptyString
  else if N.ltb b 100 then
    String (dec_char (b / 10)) (String (dec_char (b mod 10)) EmptyString)
  else
    String (dec_char (b / 100))
      (String (dec_char ((b / 10) mod 10))
        (String (dec_char (b mod 10)) EmptyString)).

(* ------------------------------------------------------------ *)
(* Word16 -> 1..4 hex digits (lowercase, no leading zeros)      *)
(* ------------------------------------------------------------ *)

Definition word16_to_hex_lower (w : word16) : string :=
  if N.ltb w 16 then String (hex_char w) EmptyString
  else if N.ltb w 256 then
    String (hex_char (w / 16)) (String (hex_char (w mod 16)) EmptyString)
  else if N.ltb w 4096 then
    String (hex_char (w / 256))
      (String (hex_char ((w / 16) mod 16))
        (String (hex_char (w mod 16)) EmptyString))
  else
    String (hex_char (w / 4096))
      (String (hex_char ((w / 256) mod 16))
        (String (hex_char ((w / 16) mod 16))
          (String (hex_char (w mod 16)) EmptyString))).

(* ------------------------------------------------------------ *)
(* String helpers                                               *)
(* ------------------------------------------------------------ *)

Fixpoint string_concat (xs : list string) : string :=
  match xs with
  | [] => EmptyString
  | s :: rest => append s (string_concat rest)
  end.

Fixpoint string_intercalate (sep : string) (xs : list string) : string :=
  match xs with
  | [] => EmptyString
  | [s] => s
  | s :: rest => append s (append sep (string_intercalate sep rest))
  end.

Fixpoint string_of_ascii_list (cs : list ascii) : string :=
  match cs with
  | [] => EmptyString
  | c :: rest => String c (string_of_ascii_list rest)
  end.

Fixpoint ascii_list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c rest => c :: ascii_list_of_string rest
  end.

Lemma string_of_ascii_list_inv :
  forall s, string_of_ascii_list (ascii_list_of_string s) = s.
Proof.
  induction s as [|c s IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma ascii_list_of_string_inv :
  forall cs, ascii_list_of_string (string_of_ascii_list cs) = cs.
Proof.
  induction cs as [|c cs IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* ------------------------------------------------------------ *)
(* Decidable equality                                           *)
(* ------------------------------------------------------------ *)

Definition byte_eqb (a b : byte) : bool := N.eqb a b.
Definition word16_eqb (a b : word16) : bool := N.eqb a b.

Lemma byte_eqb_refl : forall b, byte_eqb b b = true.
Proof. intro b; unfold byte_eqb; apply N.eqb_refl. Qed.

Lemma word16_eqb_refl : forall w, word16_eqb w w = true.
Proof. intro w; unfold word16_eqb; apply N.eqb_refl. Qed.

Lemma byte_eqb_sound : forall a b, byte_eqb a b = true -> a = b.
Proof. intros a b H; unfold byte_eqb in H; apply N.eqb_eq in H; exact H. Qed.

Lemma word16_eqb_sound : forall a b, word16_eqb a b = true -> a = b.
Proof. intros a b H; unfold word16_eqb in H; apply N.eqb_eq in H; exact H. Qed.

Fixpoint list_byte_eqb (xs ys : list byte) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => andb (byte_eqb x y) (list_byte_eqb xs' ys')
  | _, _ => false
  end.

Fixpoint list_word16_eqb (xs ys : list word16) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => andb (word16_eqb x y) (list_word16_eqb xs' ys')
  | _, _ => false
  end.

Lemma list_byte_eqb_refl : forall xs, list_byte_eqb xs xs = true.
Proof.
  induction xs as [|x xs IH]; simpl; auto.
  rewrite byte_eqb_refl, IH. reflexivity.
Qed.

Lemma list_word16_eqb_refl : forall xs, list_word16_eqb xs xs = true.
Proof.
  induction xs as [|x xs IH]; simpl; auto.
  rewrite word16_eqb_refl, IH. reflexivity.
Qed.

Lemma list_byte_eqb_sound :
  forall xs ys, list_byte_eqb xs ys = true -> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] H; simpl in H; try discriminate.
  - reflexivity.
  - apply andb_true_iff in H as [Hh Ht].
    apply byte_eqb_sound in Hh; subst.
    apply IH in Ht; subst. reflexivity.
Qed.

Lemma list_word16_eqb_sound :
  forall xs ys, list_word16_eqb xs ys = true -> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] H; simpl in H; try discriminate.
  - reflexivity.
  - apply andb_true_iff in H as [Hh Ht].
    apply word16_eqb_sound in Hh; subst.
    apply IH in Ht; subst. reflexivity.
Qed.

Definition string_eqb (s1 s2 : string) : bool :=
  if string_dec s1 s2 then true else false.

Lemma string_eqb_refl : forall s, string_eqb s s = true.
Proof. intro s; unfold string_eqb; destruct (string_dec s s); congruence. Qed.

Lemma string_eqb_iff :
  forall s1 s2, string_eqb s1 s2 = true <-> s1 = s2.
Proof.
  intros s1 s2. unfold string_eqb.
  destruct (string_dec s1 s2); split; intro; congruence.
Qed.

(* ------------------------------------------------------------ *)
(* List utilities                                               *)
(* ------------------------------------------------------------ *)

Fixpoint replicate {A} (n : nat) (x : A) : list A :=
  match n with
  | O => []
  | S n' => x :: replicate n' x
  end.

Lemma replicate_length {A} : forall n (x : A),
  List.length (replicate n x) = n.
Proof.
  induction n as [|n IH]; intro x; simpl; auto.
Qed.

Definition is_some {A} (o : option A) : bool :=
  match o with Some _ => true | None => false end.

Definition opt_bind {A B} (o : option A) (f : A -> option B) : option B :=
  match o with Some x => f x | None => None end.
