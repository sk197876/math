(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import FamilyUpdate TensorFamilyUP WordEvaluation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** The family of m copies of V, and the passage between its elements and
    sequences of length m. *)
Section PowerFamily.
Variable K : fieldType.
Variable V : lmodType K.

(** Source for [power_family]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition power_family (m : nat) : 'I_m -> lmodType K := fun _ => V.
Local Arguments power_family : clear implicits.

(** Source for [power_seq]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition power_seq m (x : {dffun forall i : 'I_m, power_family m i}) : seq V :=
  [seq (x i : V) | i <- enum 'I_m].

(** Source for [seq_power]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition seq_power (s : seq V) : {dffun forall i : 'I_(size s), power_family (size s) i} :=
  [ffun i : 'I_(size s) => nth 0 s i].

(** Source for [size_power_seq]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma size_power_seq m x : size (@power_seq m x) = m.
Proof. by rewrite size_map size_enum_ord. Qed.

(** Source for [nth_power_seq]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma nth_power_seq m x (i : 'I_m) : nth 0 (@power_seq m x) i = x i.
Proof.
rewrite (nth_map i) ?size_enum_ord //; congr (x _).
by apply: val_inj; rewrite /= nth_enum_ord.
Qed.

(** Source for [nth_power_seq_nat]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma nth_power_seq_nat m x k (hk : (k < m)%N) :
  nth 0 (@power_seq m x) k = x (Ordinal hk).
Proof. exact: (nth_power_seq x (Ordinal hk)). Qed.

(** Source for [power_seqK]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma power_seqK s : power_seq (seq_power s) = s.
Proof.
apply: (@eq_from_nth _ 0); first by rewrite size_power_seq.
move=> k; rewrite size_power_seq => hk.
by rewrite (nth_power_seq _ (Ordinal hk)) ffunE.
Qed.

(** Source for [power_seq_inj]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma power_seq_inj m : injective (@power_seq m).
Proof.
move=> x y e; apply/ffunP=> i.
by rewrite -!nth_power_seq e.
Qed.

(** Source for [power_seq_with]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma power_seq_with m x (i : 'I_m) (v : V) :
  power_seq (family_with x (v : power_family m i)) =
  take i (power_seq x) ++ v :: drop i.+1 (power_seq x).
Proof.
have hi := ltn_ord i.
apply: (@eq_from_nth _ 0).
  rewrite size_cat /= size_take size_drop !size_power_seq hi.
  by rewrite -addSnnS subnKC.
move=> k; rewrite size_power_seq => hk.
rewrite (nth_power_seq_nat _ hk) nth_cat size_take size_power_seq hi.
case: (ltngtP k i) => hki.
- rewrite nth_take // (nth_power_seq_nat _ hk) family_with_out //.
  by apply/eqP=> e; move: hki; rewrite e /= ltnn.
- rewrite -[(k - i)%N]prednK ?subn_gt0 //= nth_drop.
  have e : (i.+1 + (k - i).-1)%N = k by rewrite -subnS addnC subnK.
  rewrite e (nth_power_seq_nat _ hk) family_with_out //.
  by apply/eqP=> e'; move: hki; rewrite e' /= ltnn.
- have -> : Ordinal hk = i by exact: val_inj.
  by rewrite hki subnn family_with_in.
Qed.

(** Source for [multilinear_words_power]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma multilinear_words_power (Z : lmodType K) (beta : seq V -> Z) m :
  multilinear_words beta -> multilinear (fun x => beta (@power_seq m x)).
Proof.
move=> hb x i a v w.
by rewrite !power_seq_with hb.
Qed.
(** Source for [seq_to_power]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition seq_to_power m (s : seq V) : {dffun forall i : 'I_m, power_family m i} :=
  [ffun i : 'I_m => nth 0 s i].

(** Source for [power_seq_to_power]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma power_seq_to_power m s : size s = m -> power_seq (seq_to_power m s) = s.
Proof.
move=> hs; apply: (@eq_from_nth _ 0); first by rewrite size_power_seq.
move=> k; rewrite size_power_seq => hk.
by rewrite (nth_power_seq_nat _ hk) ffunE.
Qed.

(** Source for [seq_to_power_seq]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma seq_to_power_seq m x : seq_to_power m (power_seq x) = x.
Proof.
apply/ffunP=> i; rewrite ffunE.
exact: nth_power_seq.
Qed.

(** Source for [seq_to_power_with]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma seq_to_power_with m s t (v : V) (hi : (size s < m)%N) :
  size (s ++ v :: t) = m ->
  seq_to_power m (s ++ v :: t) =
  family_with (seq_to_power m (s ++ 0 :: t)) (v : power_family m (Ordinal hi)).
Proof.
move=> hm; have hm0 : size (s ++ 0 :: t) = m by rewrite -hm !size_cat.
apply: (@power_seq_inj m).
rewrite power_seq_with !power_seq_to_power //=.
by rewrite take_size_cat // drop_cat ltnNge leqnSn subSnn /= drop0.
Qed.

Section BetaWords.
Variable m : nat.
Variable Z : lmodType K.
Variable beta : {dffun forall i : 'I_m, power_family m i} -> Z.

(** A map on m-tuples, extended by zero to words of other lengths. *)
(** Source for [beta_words]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition beta_words (s : seq V) : Z :=
  if size s == m then beta (seq_to_power m s) else 0.

(** Source for [beta_words_multilinear]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma beta_words_multilinear : multilinear beta -> multilinear_words beta_words.
Proof.
move=> hb s t a v w; rewrite /beta_words !size_cat /=.
case: eqP => hm; last by rewrite scaler0 addr0.
have hi : (size s < m)%N by rewrite -hm -addSnnS leq_addr.
have hsz u : size (s ++ u :: t) = m by rewrite size_cat.
rewrite (seq_to_power_with hi (hsz (a *: v + w))) (seq_to_power_with hi (hsz v))
  (seq_to_power_with hi (hsz w)).
exact: (@hb (seq_to_power m (s ++ 0 :: t)) (Ordinal hi)).
Qed.

(** Source for [beta_words_zero]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma beta_words_zero s : size s != m -> beta_words s = 0.
Proof. by rewrite /beta_words => /negPf ->. Qed.

(** Source for [beta_words_power]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma beta_words_power x : beta_words (power_seq x) = beta x.
Proof. by rewrite /beta_words size_power_seq eqxx seq_to_power_seq. Qed.
End BetaWords.
End PowerFamily.
Arguments power_family {K} V m _.
