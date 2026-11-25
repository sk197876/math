(** Federer (1969), 4.1.23, p. 379:
    the original compact L1 density is approximated
    by its finite-image coefficients and their
    completed actual-cell polyhedral approximants. All
    errors use the original compact flat norm
    and the exact mass L1 size. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets cardinality reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormRegularityOperations InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading CurrentDomain CurrentSpaces CurrentCoefficientNorms
  CurrentMassSealed CurrentFlatNorm CurrentFlatCompactMonotone CurrentFlatFiniteArithmetic
  CurrentDensityAction SmoothCompactSet PolyhedralCurrentAlgebra
  CompactSummableFieldSealed CompactSummableFieldLaws CompactSummableMultivectors
  CompactSummableMultivectorDensity CompactSummableMultivectorAmbient CompactSummableFullCurrentAction
  CompactSummableAmbientFieldRepresentative CurrentFiniteImageDensityApproximation
  FiniteImageCurrentPolyhedralApproximation EuclideanFullDomainMeasure
  EuclideanLebesgueDimensions MeasureUP.
From Federer Require Import ModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section FullSummableApproximation.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Hypothesis hMN : (m<=n)%N.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation FT := (current_domain R n Full).
Local Notation V := (exterior_power X m).
Local Notation VN := (@current_vector_mass R h2 n m).
Local Notation hVN := (@current_vector_mass_real_norm R h2 n m).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation hLeb := (euclidean_lebesgue_is_measure R n).
Local Notation W := (@compact_summable_multivector_space R h2 n m Full hFull).
Local Notation value := (@compact_summable_multivector_value R h2 n m Full hFull).
Local Notation image := (@compact_summable_multivector_current R h2 n m Full hFull).
Local Notation raw := (@compact_summable_multivector_ambient_value R h2 n m Full hFull).
Local Notation Current := (@current_space R h2 n Full hFull m).
Local Notation M := (@CurrentMass.value R h2 n m Full hFull).
Variables K C : smooth_compact_set hNX Full.
Hypothesis hKC : forall x, smooth_compact_carrier K x ->
  norm_domain_interior NX (smooth_compact_carrier C) x.
Variable xi : W.
Hypothesis hOff : forall x : FT, ~smooth_compact_carrier K (set_val x) -> value xi x=0.
Local Notation F := (@current_flat_norm R h2 n m Full hFull C).

(** Source for [full_summable_field_polyhedral_approximation]:
    the original compact L1-density
    reduction of Federer 4.1.23,
    p. 379, with both printed
    flat and mass bounds. No
    smoothness or normality premise is
    added to the actual coefficient. *)
Theorem full_summable_field_polyhedral_approximation epsilon (hEpsilon : 0<epsilon) :
  exists P : Current, @polyhedral_current_subspace R h2 n m Full hFull C P /\
    (F (image xi-P)<=epsilon%:E)%E /\ (M P<=M (image xi)+epsilon%:E)%E.
Proof.
pose delta := epsilon/3.
have hThree : (0<(3:R)) by rewrite ltr0n.
have hDelta : 0<delta := divr_gt0 hEpsilon hThree.
have hBudget : delta+delta<=epsilon by rewrite /delta; lra.
have [eta [hFinite [hEtaOff [_ [hError hMassEta]]]]] :=
  @current_finite_image_density_approximation R h2 n m Full hFull xi K delta hOff hDelta.
have [f [hRaw hSize]] := @compact_summable_ambient_field_representative R h2 n m eta.
pose valueA := @compact_summable_field_value R XT V VN hVN Leb hLeb.
have hFiniteA : finite_set (valueA f @` setT).
  apply: (sub_finite_set _ hFinite)=> y [x _ <-].
  pose p := @euclidean_full_domain_point R n x.
  exists p; first exact: Logic.I.
  have hInside := @compact_summable_multivector_ambient_inside R h2 n m Full hFull eta p.
  change (raw eta x=value eta p) in hInside.
  by rewrite /valueA hRaw hInside.
have hOffA x : ~smooth_compact_carrier K x -> valueA f x=0.
  move=> hx; rewrite /valueA hRaw.
  pose p := @euclidean_full_domain_point R n x.
  have hInside := @compact_summable_multivector_ambient_inside R h2 n m Full hFull eta p.
  change (raw eta x=value eta p) in hInside.
  rewrite hInside; exact: (@hEtaOff p hx).
have hDensity := @compact_summable_full_current_action R h2 n m eta.
rewrite -hRaw in hDensity.
have [P [hPoly [hApprox hMass]]] := @finite_image_current_polyhedral_approximation
  R h2 n m hMN K C hKC f hFiniteA hOffA (image eta) hDensity delta hDelta.
have hInclusion : smooth_compact_carrier K `<=` smooth_compact_carrier C.
  move=> x hx; exact: (@norm_domain_interior_member R X NX hNX
    (smooth_compact_carrier C) x (@hKC x hx)).
have hFirst : (F (image xi-image eta)<delta%:E)%E.
  exact: le_lt_trans (@current_flat_compact_monotone R h2 n m Full hFull K C
    hInclusion (image xi-image eta)) hError.
have hTriangle := @current_flat_finite_triangle R h2 n m Full hFull C
  (image xi-image eta) (image eta-P)
  (lt_trans hFirst (ltry delta)) (le_lt_trans hApprox (ltry delta)).
have hDifference : (image xi-image eta)+(image eta-P)=image xi-P by rewrite addrA subrK.
rewrite hDifference in hTriangle.
have hErrorSum := leeD (ltW hFirst) hApprox.
rewrite -EFinD in hErrorSum.
exists P; split; first exact: hPoly.
split.
- apply: (le_trans (le_trans hTriangle hErrorSum)); by rewrite lee_fin.
- have hMassEnlarge := leeD hMassEta (lexx delta%:E).
  apply: (le_trans (le_trans hMass hMassEnlarge)).
  rewrite -addeA -EFinD; apply: leeD; first exact: lexx.
  by rewrite lee_fin.
Qed.
End FullSummableApproximation.
