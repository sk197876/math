(** Federer (1969), 1.8.2, p. 40: at most m orthonormal
    pairs fit in a 2m-dimensional associated space. When there are
    exactly m pairs, they form a basis. These are supporting dimension
    steps for the alternating normal form from 1.7.3, pp. 29-30. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP OrthonormalFamilies SkewNormalFormUP
  FiniteIndependence LinearBasis FiniteDimension FiniteBasisComparison FiniteBasisCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Dimension.
Variable R : realFieldType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable m : nat.
Variable e : 'I_(m+m) -> V.
Hypothesis he : is_basis e.
Variable k : nat.
Variables a b : 'I_k -> V.
Hypothesis ho : orthonormal_family B (paired_family a b).
Local Notation I := (Finite.clone ('I_k * bool)%type _).
Local Notation VF := (finite_basis_vect he).

(** Source for [orthonormal_pairs_dimension_bound]: Federer 1.8.2,
    p. 40, the number of orthonormal pairs is at most half the
    real dimension, including the zero-dimensional case. *)
Theorem orthonormal_pairs_dimension_bound : (k <= m)%N.
Proof.
have hi := orthonormal_independent hB ho.
have he' : finite_independent (fun i : 'I_(#|I|) => paired_family a b (enum_val i)).
  exact: finite_independent_reindex (@enum_valK I) (@enum_rankK I) hi.
have hd := @finite_independent_dimension R VF #|I|
  (fun i => paired_family a b (enum_val i)) he'.
rewrite finite_basis_dimension card_ord card_prod card_ord card_bool in hd.
by move: hd; rewrite muln2 addnn leq_double.
Qed.

(** Source for [orthonormal_pairs_full_basis]: Federer 1.8.2,
    p. 40, a full family of m orthonormal pairs is a basis of
    the 2m-dimensional associated space. *)
Theorem orthonormal_pairs_full_basis : k = m -> is_basis (paired_family a b).
Proof.
move=> hk; have hi := orthonormal_independent hB ho.
apply: (@finite_independent_basis_card R VF I (paired_family a b)).
- by rewrite finite_basis_dimension card_ord card_prod card_ord card_bool muln2 -addnn hk.
- exact hi.
Qed.
End Dimension.
