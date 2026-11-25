(** Federer (1969), 4.1.23, p. 379: the
    finite-image L1 approximation gives the stated
    mass and flat approximations of the actual
    density current. The original U and same
    compact coefficient carrier are preserved exactly. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  CurrentDomain CurrentSpaces CurrentCoefficientNorms CurrentSupportGeometry
  SmoothCompactSet SubtypeCompactHausdorff CurrentMassSealed CurrentFlatNorm
  CurrentFlatMassComparison CompactSummableFieldLaws CompactSummableMultivectors
  CompactSummableMultivectorDensity CompactSummableMultivectorDifference
  CompactSummableMultivectorSupport CompactSummableFiniteImageApproximation
  EuclideanOpenDomainMeasure MeasureUP RadonMeasureBounds.
From Federer Require Import IsotropyGroupTopology RadonBorelRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section FiniteImageCurrentApproximation.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation V := (exterior_power X m).
Local Notation VN := (@current_vector_mass R h2 n m).
Local Notation hVN := (@current_vector_mass_real_norm R h2 n m).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation UT := (current_domain R n U).
Local Notation mu := (@euclidean_open_domain_measure R n U).
Local Notation hMu := (@euclidean_open_domain_measure_laws R n U hU).1.
Local Notation hRadon := (@euclidean_open_domain_measure_laws R n U hU).2.
Local Notation W := (@compact_summable_multivector_space R h2 n m U hU).
Local Notation value := (@compact_summable_multivector_value R h2 n m U hU).
Local Notation size := (@compact_summable_multivector_size R h2 n m U hU).
Local Notation image := (@compact_summable_multivector_current R h2 n m U hU).
Local Notation M := (@CurrentMass.value R h2 n m U hU).
Local Notation support := (@current_support R h2 n U hU m).

(** Source for [current_finite_image_density_approximation]:
    the third reduction of Federer 4.1.23,
    p. 379, with its two quantitative
    errors and mass budget. Both coefficient
    fields stay in the original Omega space,
    and the finite-image field vanishes pointwise
    outside the same K. *)
Theorem current_finite_image_density_approximation
    (xi : W) (K : smooth_compact_set hNX U) (epsilon : R) :
  (forall x : UT, ~smooth_compact_carrier K (set_val x) -> value xi x=0) ->
  0<epsilon ->
  exists eta : W,
    finite_set (value eta @` setT) /\
    (forall x : UT, ~smooth_compact_carrier K (set_val x) -> value eta x=0) /\
    (M (image xi-image eta)%R<epsilon%:E)%E /\
    (@current_flat_norm R h2 n m U hU K (image xi-image eta)%R<epsilon%:E)%E /\
    (M (image eta)<=M (image xi)+epsilon%:E)%E.
Proof.
move=> hOff hEpsilon.
pose KT : set UT := [set x | smooth_compact_carrier K (set_val x)].
have hKT : compact KT := @set_type_compact_preimage XT U
  (smooth_compact_carrier K) (smooth_compact_is_compact K) (smooth_compact_in_domain K).
have hKTMeas : measure_measurable mu KT := radon_compact_measurable hMu hRadon hKT.
have [eta [hFinite [hEtaOff hError]]] :=
  @compact_summable_finite_image_approximation R UT V VN hVN mu hMu
    xi KT epsilon hKT hKTMeas hOff hEpsilon.
have hMassError : (M (image xi-image eta)%R<epsilon%:E)%E.
  rewrite (@compact_summable_multivector_current_difference_mass R h2 n m U hU xi eta)
    lte_fin; exact: hError.
have hXiSupport := @compact_summable_multivector_current_support R h2 n m U hU xi K hOff.
have hEtaSupport := @compact_summable_multivector_current_support R h2 n m U hU eta K hEtaOff.
have hDifferenceSupport : support (image xi-image eta)%R `<=` smooth_compact_carrier K.
  have h := @current_support_linear_subset R h2 n m U hU K
    (-1) (image eta) (image xi) hEtaSupport hXiSupport.
  by rewrite scaleN1r addrC in h.
have hFlatError := le_lt_trans (@current_flat_norm_le_mass R h2 n m U hU K
  (image xi-image eta)%R hDifferenceSupport) hMassError.
have hSize := @compact_summable_multivector_size_laws R h2 n m U hU.
have hTriangle := real_seminorm_triangle hSize xi (eta-xi)%R.
have hIdentity : xi+(eta-xi)=eta by rewrite addrC subrK.
rewrite hIdentity (real_seminorm_subtract hSize eta xi) in hTriangle.
have hBound : size eta<=size xi+epsilon.
  exact: le_trans hTriangle (lerD (lexx (size xi)) (ltW hError)).
exists eta; split; first exact: hFinite.
split; first exact: hEtaOff.
split; first exact: hMassError.
split; first exact: hFlatError.
rewrite !compact_summable_multivector_current_mass -EFinD lee_fin.
exact: hBound.
Qed.
End FiniteImageCurrentApproximation.
