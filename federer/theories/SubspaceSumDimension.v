(** Federer (1969), 1.6.3, p. 25, dimension step in the intersection
    corollary. This module proves the direct-sum dimension criterion using
    bases, without choosing matrix representations for the given subspaces. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors SubspaceBasisProduct SpanningDimension.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Sum.
Variable K : fieldType.
Variable V : lmodType K.
Variables S T P : subspace V.
Hypothesis hP : forall v, P v <-> exists x y, S x /\ T y /\ v=x+y.
Variables k l d : nat.
Variable a : 'I_k -> subspace_space S.
Variable b : 'I_l -> subspace_space T.
Variable z : 'I_d -> subspace_space P.
Hypotheses (ha : is_basis a) (hb : is_basis b) (hz : is_basis z).
Local Notation av := (fun i => subspace_val (a i)).
Local Notation bv := (fun i => subspace_val (b i)).
Local Notation c := (concatenate_family av bv).

(** Source for [sum_family_in]: Federer 1.6.3, p. 25, sum of
    annihilators. Supporting fact: concatenating bases of the two
    summands gives a family in their sum. *)
Lemma sum_family_in i : P (c i).
Proof.
apply: (proj2 (hP _)); case: (split_ordP i) => [j ->|j ->].
- rewrite concatenate_family_l; exists (av j), 0; split; first exact: subspace_valP.
  split; first exact: subspace_zero; by rewrite addr0.
- rewrite concatenate_family_r; exists 0, (bv j); split; first exact: subspace_zero.
  split; first exact: subspace_valP; by rewrite add0r.
Qed.

(** Source for [sum_family_spans]: Federer 1.6.3, p. 25, dimension
    of a sum. Supporting fact: the concatenated family spans the sum. *)
Lemma sum_family_spans : forall v : subspace_space P,
  in_finite_span (subspace_family sum_family_in) v.
Proof.
apply: subspace_family_spans => v hv.
have [x [y [hs [ht hxy]]]] := proj1 (hP v) hv.
apply: (proj2 (concatenate_family_span av bv v)).
exists x, y; split.
- exact: (proj2 (@subspace_basis_span K V S k a ha x) hs).
- split=> //; exact: (proj2 (@subspace_basis_span K V T l b hb y) ht).
Qed.

(** Source for [sum_family_independent]: Federer 1.6.3, p. 25,
    direct-sum dimension criterion. Supporting equivalence: the
    concatenation is independent exactly when the summands intersect
    only in zero. *)
Lemma sum_family_independent :
  finite_independent (subspace_family sum_family_in) <->
    forall v, S v -> T v -> v=0.
Proof.
split.
- move=> hc v hs ht.
  have hc' : finite_independent c.
    exact: finite_independent_map (@subspace_val_injective K V P) hc.
  apply: (@independent_concatenation_disjoint K V k l av bv hc' v).
  + exact: (proj2 (@subspace_basis_span K V S k a ha v) hs).
  + exact: (proj2 (@subspace_basis_span K V T l b hb v) ht).
- move=> hST; apply: subspace_family_independent.
  have ha' := finite_independent_map (@subspace_val_injective K V S) (finite_basis_independent ha).
  have hb' := finite_independent_map (@subspace_val_injective K V T) (finite_basis_independent hb).
  apply: disjoint_concatenation_independent ha' hb' _ => v hs ht.
  apply: hST.
  + exact: (proj1 (@subspace_basis_span K V S k a ha v) hs).
  + exact: (proj1 (@subspace_basis_span K V T l b hb v) ht).
Qed.

(** Source for [sum_dimension_iff_disjoint]: Federer 1.6.3, p. 25, dimension
    argument in the corollary. Direct supporting criterion: the dimension of
    a sum equals the sum of the dimensions iff the summands intersect only
    in zero. *)
Theorem sum_dimension_iff_disjoint :
  (k+l=d)%N <-> forall v, S v -> T v -> v=0.
Proof.
rewrite -sum_family_independent.
symmetry; exact: (@spanning_independent_iff_size K (subspace_space P)
  d z hz (k+l) (subspace_family sum_family_in) sum_family_spans).
Qed.
End Sum.
