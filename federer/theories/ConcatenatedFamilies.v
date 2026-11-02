(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDecomposition.
From Federer Require Import FiniteSpans.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1, third corollary: concatenate the two ordered families
    of factors, preserving the order in xi wedge eta. *)
(** Source for [concatenate_family]: Federer (1969), 1.6.1, p. 24, third
    corollary. In words: The wedge of two nonzero simple vectors is nonzero
    exactly when its associated subspace is the direct sum of their
    associated subspaces. Definition or construction used to formalise this
    passage. *)
Definition concatenate_family (T : Type) m n (e : 'I_m -> T) (f : 'I_n -> T)
  (i : 'I_(m+n)) := match split i with inl j => e j | inr j => f j end.
(** Source for [concatenate_family_l]: Federer (1969), 1.6.1, p. 24, third
    corollary. In words: The wedge of two nonzero simple vectors is nonzero
    exactly when its associated subspace is the direct sum of their
    associated subspaces. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma concatenate_family_l (T : Type) m n (e : 'I_m -> T) (f : 'I_n -> T) i :
  concatenate_family e f (lshift n i) = e i.
Proof.
change (match split (unsplit (inl i : 'I_m + 'I_n)) with inl j => e j | inr j => f j end = e i).
by rewrite unsplitK.
Qed.
(** Source for [concatenate_family_r]: Federer (1969), 1.6.1, p. 24, third
    corollary. In words: The wedge of two nonzero simple vectors is nonzero
    exactly when its associated subspace is the direct sum of their
    associated subspaces. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma concatenate_family_r (T : Type) m n (e : 'I_m -> T) (f : 'I_n -> T) i :
  concatenate_family e f (rshift m i) = f i.
Proof.
change (match split (unsplit (inr i : 'I_m + 'I_n)) with inl j => e j | inr j => f j end = f i).
by rewrite unsplitK.
Qed.
(** Source for [concatenate_family_sequence]: Federer (1969), 1.6.1, p. 24,
    third corollary. In words: The wedge of two nonzero simple vectors is
    nonzero exactly when its associated subspace is the direct sum of their
    associated subspaces. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma concatenate_family_sequence (T : Type) m n (e : 'I_m -> T) (f : 'I_n -> T) :
  [seq concatenate_family e f i | i <- enum 'I_(m+n)] =
  [seq e i | i <- enum 'I_m] ++ [seq f i | i <- enum 'I_n].
Proof.
rewrite enum_ord_cat map_cat -!map_comp; congr (_ ++ _);
  apply: eq_map => i; rewrite /= ?concatenate_family_l ?concatenate_family_r //.
Qed.
Section Sums.
Variable K : fieldType.
Variable V : lmodType K.
Variables m n : nat.
Variables (e : 'I_m -> V) (f : 'I_n -> V).
(** Source for [concatenate_family_sum]: Federer (1969), 1.6.1, p. 24, third
    corollary. In words: The wedge of two nonzero simple vectors is nonzero
    exactly when its associated subspace is the direct sum of their
    associated subspaces. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma concatenate_family_sum (c : 'I_(m+n) -> K) :
  (\sum_i c i *: concatenate_family e f i) =
    (\sum_i c (lshift n i) *: e i) + (\sum_i c (rshift m i) *: f i).
Proof.
rewrite big_split_ord; congr (_ + _); apply: eq_bigr => i _;
  by rewrite ?concatenate_family_l ?concatenate_family_r.
Qed.
(** Source for [concatenate_family_combination]: Federer (1969), 1.6.1, p.
    24, third corollary. In words: The wedge of two nonzero simple vectors
    is nonzero exactly when its associated subspace is the direct sum of
    their associated subspaces. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma concatenate_family_combination (a : 'I_m -> K) (b : 'I_n -> K) :
  (\sum_i concatenate_family a b i *: concatenate_family e f i) =
    (\sum_i a i *: e i) + (\sum_i b i *: f i).
Proof.
rewrite concatenate_family_sum; congr (_ + _); apply: eq_bigr => i _;
  by rewrite ?concatenate_family_l ?concatenate_family_r.
Qed.
(** Source for [concatenate_family_span]: Federer (1969), 1.6.1, p. 24,
    third corollary. In words: The wedge of two nonzero simple vectors is
    nonzero exactly when its associated subspace is the direct sum of their
    associated subspaces. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma concatenate_family_span v : in_finite_span (concatenate_family e f) v <->
  exists x y : V, in_finite_span e x /\ in_finite_span f y /\ v=x+y.
Proof.
split.
- move=> [c hc]; exists (\sum_i c (lshift n i) *: e i), (\sum_i c (rshift m i) *: f i).
  split; first by exists (fun i => c (lshift n i)).
  split; first by exists (fun i => c (rshift m i)).
  by rewrite -concatenate_family_sum.
- move=> [x [y [[a ha] [[b hb] ->]]]].
  exists (concatenate_family a b); by rewrite concatenate_family_combination -ha -hb.
Qed.
End Sums.
