(** Federer (1969), 4.1.23, p. 379:
    the normal-input theorem on full Euclidean space
    follows from the original compact smoothing and
    the completed compact L1-density approximation.
    The smoothing does not increase mass, and
    the above-dimensional endpoint is treated before selection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain CurrentSpaces CurrentMassSealed CurrentFlatNorm CurrentFlatFiniteArithmetic
  NormalCurrentsUP SmoothCompactSet PolyhedralCurrentAlgebra
  PolyhedralApproximationUP PolyhedralApproximationEndpoints
  CompactSummableMultivectors CompactSummableMultivectorDensity
  NormalFullSmoothCoefficientApproximation FullSummableFieldPolyhedralApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section FullNormalApproximation.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation Current := (@current_space R h2 n Full hFull m).
Local Notation M := (@CurrentMass.value R h2 n m Full hFull).
Local Notation image := (@compact_summable_multivector_current R h2 n m Full hFull).
Variables K C : smooth_compact_set hNX Full.
Hypothesis hKC : forall x, smooth_compact_carrier K x ->
  norm_domain_interior NX (smooth_compact_carrier C) x.
Variable T : Current.
Hypothesis hNormal : @normal_currents_supported_in R h2 n Full hFull m K T.
Local Notation F := (@current_flat_norm R h2 n m Full hFull C).

(** Source for [normal_full_polyhedral_approximation]:
    the normal-current reduction in
    Federer 4.1.23, p. 379,
    now has both required bounds
    in the original compact C.
    Every degree, empty compact and
    zero-dimensional ambient space is retained;
    C need not be convex. *)
Theorem normal_full_polyhedral_approximation epsilon (hEpsilon : 0<epsilon) :
  exists P : Current,
    @is_polyhedral_flat_mass_approximation R h2 n m Full hFull C T epsilon P.
Proof.
case: (leqP m n)=> hMN; last first.
  exists 0; exact: (@polyhedral_above_dimension_approximation R h2 n m Full hFull
    C T epsilon hMN (ltW hEpsilon)).
pose delta := epsilon/3.
have hThree : (0<(3:R)) by rewrite ltr0n.
have hDelta : 0<delta := divr_gt0 hEpsilon hThree.
have hBudget : delta+delta<=epsilon by rewrite /delta; lra.
have hDeltaLe : delta<=epsilon by rewrite /delta; lra.
have [f [xi [L [_ [hLC [hOff [hError hMass]]]]]]] :=
  @normal_full_smooth_coefficient_approximation R h2 n m K C T delta hKC hNormal hDelta.
have [P [hPoly [hApprox hMassP]]] := @full_summable_field_polyhedral_approximation R h2 n m
  hMN L C hLC xi hOff delta hDelta.
have hTriangle := @current_flat_finite_triangle R h2 n m Full hFull C
  (T-image xi) (image xi-P) (lt_trans hError (ltry delta)) (le_lt_trans hApprox (ltry delta)).
have hDifference : (T-image xi)+(image xi-P)=T-P by rewrite addrA subrK.
rewrite hDifference in hTriangle.
have hErrorSum := leeD (ltW hError) hApprox.
rewrite -EFinD in hErrorSum.
exists P; split; first exact: hPoly.
split.
- apply: (le_trans (le_trans hTriangle hErrorSum)); by rewrite lee_fin.
- have hMassEnlarge := leeD hMass (lexx delta%:E).
  apply: (le_trans (le_trans hMassP hMassEnlarge)).
  apply: leeD; first exact: lexx.
  by rewrite lee_fin.
Qed.
End FullNormalApproximation.
