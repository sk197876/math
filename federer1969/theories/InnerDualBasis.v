(** Federer (1969), 1.7.2, pp. 28-29: polarity maps orthonormal bases to
    dual orthonormal bases. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerPolarity OrthonormalFamilies
  LinearBasis FiniteIndependence FiniteBasisCriterion FiniteBasisComparison
  Annihilator FiniteDualDimension Hom AlternatingCoordinates.
From Federer Require Import InnerDual InnerPolaritySurjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section DualBasis.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.

(** Source for [inner_polarity_basis]: Federer 1.7.2, pp. 28-29,
    supporting basis transfer through the polarity isomorphism. *)
Theorem inner_polarity_basis : is_basis (fun i => inner_polarity hB (e i)).
Proof.
apply: finite_basis_criterion.
- exact (@finite_independent_map R (Finite.clone 'I_n _) V (A_m V R^o 1)
    (inner_polarity hB) e (@inner_polarity_injective R V B hB) (finite_basis_independent he)).
- move=> a; have [x <-] := @inner_polarity_surjective R V B hB n e he a.
  exists (fun i => dual_basis he i x).
  rewrite {1}(basis_vector_expansion he x) linear_sum.
  by under eq_bigr do rewrite linearZ.
Qed.

(** Source for [inner_polarity_orthonormal_basis]: Federer 1.7.2,
    pp. 28-29, the image of an orthonormal basis is an orthonormal
    basis for the induced dual inner product. Its identification with
    the dual basis is [inner_polarity_orthonormal_dual]. *)
Theorem inner_polarity_orthonormal_basis : orthonormal_family B e ->
  is_basis (fun i => inner_polarity hB (e i)) /\
  orthonormal_family (inner_dual_product hB he) (fun i => inner_polarity hB (e i)).
Proof.
move=> ho; split; first exact: inner_polarity_basis.
move=> i j; by rewrite inner_dual_polarityE ho.
Qed.
End DualBasis.
