(** Federer (1969), 4.1.19, p. 377: the
    class-one exterior derivative satisfies the original
    weak equation. Approximate the form and its
    actual exterior derivative by the already proved
    compact smooth tests on the unchanged coefficient
    support. No finite measure of U is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra
  functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import AlternatingForms Hom Bilinear RealNormUP NormMetric
  NormDifferentialUP NormClassOneUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  AlternatingPairing ExteriorDerivativeUP CurrentDomain CurrentSpaces
  CurrentCoefficientNorms CurrentVectorSpaces CurrentEvaluation
  CurrentPointEvaluation CurrentBoundary CurrentTestExteriorDerivative
  CurrentClassOneTestApproximation SmoothCompactSet SmoothFunctionSupport
  SmoothCurrentDivergence CurrentCovectorDual EuclideanOpenDomainMeasure
  CompactSummableMultivectors CompactSummableMultivectorDensity
  CompactSummableMultivectorLinear CurrentLonePairImageUP
  CurrentLonePairImageSealed CurrentLonePairCost
  CurrentCompactSmoothDivergenceSupport CurrentCompactSmoothDivergenceKernel
  MeasureIntegralUP SummableRealFunctionUP FlatCochainRepresentationUP
  BoundedPairFormFunctional CurrentWeakExteriorPairUP
  WeakExteriorPairGraphAction CompactSummableDualUniformIntegral
  ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ClassOneWeakIntegral.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Y d := (A_m X R^o d).
Local Notation N d := (@current_form_comass R h2 n d).
Local Notation hN d := (@current_form_comass_real_norm R h2 n d).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation UT := (current_domain R n U).
Local Notation P := (@current_lone_pair_space R h2 n m U hU).
Local Notation Q := (@CurrentLonePair.map R h2 n m U hU).
Local Notation J := (@current_lone_pair_cost R h2 n m U hU).
Local Notation value d := (@compact_summable_multivector_value R h2 n d U hU).
Local Notation size d := (@compact_summable_multivector_size R h2 n d U hU).
Local Notation image d := (@compact_summable_multivector_current R h2 n d U hU).
Local Notation ev d := (@current_vector_smooth_value R h2 n U hU d).
Local Notation hE d := (@current_vector_smooth_space_laws R h2 n U hU d).
Local Notation div := (@smooth_current_divergence R h2 n m U hU).
Local Notation test d := (@current_test_value R h2 n U hU d).
Local Notation d := (@current_test_exterior_derivative R h2 n m U hU).
Local Notation action k := (@current_value R h2 n U hU k).
Local Notation mu := (@euclidean_open_domain_measure R n U).
Local Notation hMu := (proj1 (@euclidean_open_domain_measure_laws R n U hU)).

(** Source for [current_class_one_bounded_exterior_weak_integral]:
    the class-one implication in the parenthesis
    of Federer 4.1.19, p. 377,
    first when both actual fields are bounded.
    This supporting lemma is used after compact
    localization for a merely locally bounded derivative;
    the weak relation itself retains every original eta. *)
Theorem current_class_one_bounded_exterior_weak_integral
    (phi : X -> Y m) (beta : X -> Y m.+1) :
  norm_class hNX (hN m) U phi 1%N ->
  (forall x, U x -> has_exterior_derivative NX (N m) U phi x (beta x)) ->
  @is_bounded_measurable_current_form R h2 n U m
    (fun x : UT => phi (set_val x)) ->
  @is_bounded_measurable_current_form R h2 n U m.+1
    (fun x : UT => beta (set_val x)) ->
  @is_weak_current_exterior_pair R h2 n m U hU
    (fun x : UT => phi (set_val x))
    (fun x : UT => beta (set_val x)).
Proof.
move=> hClass hBeta hPhiBounded hBetaBounded.
have [F [c [hC [hBound hDensity]]]] :=
  @bounded_pair_form_functional_exists R h2 n m U hU
    (fun x : UT => phi (set_val x))
    (fun x : UT => beta (set_val x)) hPhiBounded hBetaBounded.
apply: ((@weak_exterior_pair_graph_action_iff R h2 n m U hU F
  (fun x : UT => phi (set_val x))
  (fun x : UT => beta (set_val x)) hDensity).2).
move=> v hGraph.
have [eta [K [hSupport [hLeft hRight]]]] := hGraph.
have hDivSupport := @current_compact_smooth_divergence_support R h2 n m
  U hU K eta hSupport.
have hXiOff (x : UT) (hx : ~smooth_compact_carrier K (set_val x)) :
    value m v.1 x=0.
  rewrite hLeft.
  exact: ((smooth_function_compact_support_iff (hE m) K (div eta)).1
    hDivSupport (set_val x) hx).
have hEtaOff (x : UT) (hx : ~smooth_compact_carrier K (set_val x)) :
    value m.+1 v.2 x=0.
  rewrite hRight.
  exact: ((smooth_function_compact_support_iff (hE m.+1) K eta).1
    hSupport (set_val x) hx).
have hKernel := @current_compact_smooth_divergence_pair_kernel R h2 n m U hU v hGraph.
have [A hApprox] := @current_class_one_test_approximation R h2 n m U hU
  K phi beta hClass hBeta.
have hSmall error (hError : 0<error) : `|F v| <= error*J v.
  have [r [hR hUniform]] := @hApprox error hError.
  have hHalf : 0<r/2 by rewrite divr_gt0 // ltr0n.
  have hHalfR : r/2<r by lra.
  pose a := action m (image m v.1) (A (r/2)).
  pose b := action m.+1 (image m.+1 v.2) (d (A (r/2))).
  have hTestLeft := @compact_summable_multivector_current_action R h2 n m U hU
    v.1 (A (r/2)).
  have hTestRight := @compact_summable_multivector_current_action R h2 n m.+1 U hU
    v.2 (d (A (r/2))).
  have hUniformLeft (x : UT) (hx : smooth_compact_carrier K (set_val x)) :
      N m (phi (set_val x)-test m (A (r/2)) (set_val x)) <= error.
    rewrite (real_seminorm_subtract (hN m).1).
    exact: (ltW (@hUniform (r/2) hHalf hHalfR (set_val x) hx).1).
  have hUniformRight (x : UT) (hx : smooth_compact_carrier K (set_val x)) :
      N m.+1 (beta (set_val x)-test m.+1 (d (A (r/2))) (set_val x)) <= error.
    rewrite (real_seminorm_subtract (hN m.+1).1).
    exact: (ltW (@hUniform (r/2) hHalf hHalfR (set_val x) hx).2).
  have hFirst := @compact_summable_dual_uniform_integral_error R UT
    (exterior_power X m) (Y m) (@current_vector_mass R h2 n m)
    (@current_vector_mass_real_norm R h2 n m)
    (@current_covector_evaluation R n m) (N m)
    (@current_covector_continuous_dual R h2 n m) mu hMu v.1
    (fun x : UT => smooth_compact_carrier K (set_val x))
    (fun x : UT => phi (set_val x))
    (fun x : UT => test m (A (r/2)) (set_val x))
    (F (v.1,0)) a error hXiOff (hDensity.2.2.1 v.1) hTestLeft hUniformLeft.
  have hSecond := @compact_summable_dual_uniform_integral_error R UT
    (exterior_power X m.+1) (Y m.+1) (@current_vector_mass R h2 n m.+1)
    (@current_vector_mass_real_norm R h2 n m.+1)
    (@current_covector_evaluation R n m.+1) (N m.+1)
    (@current_covector_continuous_dual R h2 n m.+1) mu hMu v.2
    (fun x : UT => smooth_compact_carrier K (set_val x))
    (fun x : UT => beta (set_val x))
    (fun x : UT => test m.+1 (d (A (r/2))) (set_val x))
    (F (0,v.2)) b error hEtaOff (hDensity.2.2.2 v.2) hTestRight hUniformRight.
  have hZero : a+b=0.
    pose E := @current_point_evaluation R h2 n m U hU (A (r/2)).
    have h := congr1 E hKernel.
    rewrite (@CurrentLonePair.laws R h2 n m U hU v)
      (linD (hom_linear E)) (lin0 (hom_linear E)) in h.
    change (a+action m
      (@current_boundary R h2 n m U hU (image m.+1 v.2)) (A (r/2))=0) in h.
    rewrite current_boundary_evaluation in h.
    exact: h.
  have hPair : ((v.1,0):P)+(0,v.2)=v.
    apply: injective_projections.
    - change (v.1+0=v.1); exact: addr0.
    - change (0+v.2=v.2); exact: add0r.
  have hValue : F v=(F (v.1,0)-a)+(F (0,v.2)-b).
    have h := linD (hom_linear F) (v.1,0) (0,v.2).
    rewrite hPair in h.
    lra.
  rewrite hValue.
  have hSum := le_trans (ler_normD _ _) (lerD hFirst hSecond).
  by rewrite -mulrDr in hSum.
have hCost : 0<=J v := real_seminorm_nonnegative
  (@current_lone_pair_cost_seminorm R h2 n m U hU) v.
have hZero : ((`|F v|)%:E<=0%E)%E.
  apply: (@extended_upper_bound_from_scaled_errors R (`|F v|)%:E 0 (J v) hCost)
    => error hError.
  by rewrite add0r mulrC lee_fin; exact: hSmall.
rewrite lee_fin in hZero.
apply/eqP; rewrite -normr_eq0; apply/eqP.
apply/eqP; by rewrite eq_le hZero normr_ge0.
Qed.
End ClassOneWeakIntegral.
