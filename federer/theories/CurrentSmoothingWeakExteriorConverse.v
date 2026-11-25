(** Federer (1969), 4.1.19, p. 377: if
    the actual smooth convolutions obey the exterior
    equation on every valid kernel locus, the original
    measurable forms obey the printed weak equation.
    Compact test convergence avoids any boundary equation
    for the total zero extensions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormClassOneUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms
  AlternatingPairing CurrentDomain CurrentCoefficientNorms CurrentCoefficientCompleteness
  CurrentVectorSpaces CurrentCovectorDual SmoothFunctionSpaceUP SmoothFunctionDerivativesUP
  SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology SmoothCompactSet
  CompactContinuousVectorZeroExtension CurrentLonePairImageUP CompactSummableMultivectors
  FlatCochainRepresentationUP BoundedPairFormFunctional CurrentWeakExteriorPairUP
  WeakExteriorPairGraphAction CurrentCompactGraphTests CurrentPairDensityFullTestAction
  BoundedCurrentFormSmoothing CurrentFormFieldDistribution CurrentFormSmoothingTestLimit
  CurrentSmoothWeakTestOnKernelLocus CurrentCompactClosedTubeInside EuclideanClosedSupportTube
  ClosedBallContainmentOpen ExteriorDerivativeUP SmoothingKernelUP SmoothingDilationUP
  SmoothingDilationSmooth SmoothingDilationNonzeroRadius SmoothingConvolutionUP
  CompactSmoothConvolutionSmoothness EuclideanLebesgueDimensions MeasureIntegralUP
  MeasureIntegralUniqueness SummableRealFunctionUP SummableRealArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SmoothingConverse.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation Y d := (A_m X R^o d).
Local Notation YN d := (@current_form_comass R h2 n d).
Local Notation hYN d := (@current_form_comass_real_norm R h2 n d).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation E d := (@current_vector_smooth_space R h2 n Full hFull d).
Local Notation hE d := (@current_vector_smooth_space_laws R h2 n Full hFull d).
Local Notation DT d := (smooth_test_space (hE d)).
Local Notation tv d := (smooth_test_value (hE d)).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation hLeb := (euclidean_lebesgue_is_measure R n).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation UT := (current_domain R n U).
Local Notation P := (@current_lone_pair_space R h2 n m U hU).
Variables (phi : UT -> Y m) (psi : UT -> Y m.+1).
Local Notation extensionPhi := (@compact_vector_open_extension R XT U (Y m) phi).
Local Notation extensionPsi := (@compact_vector_open_extension R XT U (Y m.+1) psi).
Variables (kernel : X -> R) (family : R -> X -> R).
Hypothesis hKernel : is_smoothing_kernel kernel.
Hypothesis hFamily : is_smoothing_dilation kernel family.

(** Source for [current_smoothing_weak_exterior_converse]:
    the reverse implication in the convolution
    criterion of Federer 4.1.19, p. 377,
    for the original open U and actual
    ordinary coefficient convolutions. All measurable
    representatives and every original graph test are retained. *)
Theorem current_smoothing_weak_exterior_converse
    (g : R -> X -> Y m) (h : R -> X -> Y m.+1) :
  @is_bounded_measurable_current_form R h2 n U m phi ->
  @is_bounded_measurable_current_form R h2 n U m.+1 psi ->
  (forall epsilon, 0<epsilon ->
    is_smoothing_convolution (hYN m) (family epsilon) extensionPhi (g epsilon)) ->
  (forall epsilon, 0<epsilon ->
    is_smoothing_convolution (hYN m.+1) (family epsilon) extensionPsi (h epsilon)) ->
  (forall epsilon, 0<epsilon -> forall z,
    norm_closed_ball_containment U epsilon z ->
    has_exterior_derivative NX (YN m) U (g epsilon) z (h epsilon z)) ->
  @is_weak_current_exterior_pair R h2 n m U hU phi psi.
Proof.
move=> hPhi hPsi hG hH hEquation.
have hFieldPhi := @bounded_current_form_extension_locally_integrable
  R h2 n m U hU phi hPhi.
have hFieldPsi := @bounded_current_form_extension_locally_integrable
  R h2 n m.+1 U hU psi hPsi.
have [T [hT hTAction]] :=
  @current_form_field_distribution_exists R h2 n m extensionPhi hFieldPhi.
have [S [hS hSAction]] :=
  @current_form_field_distribution_exists R h2 n m.+1 extensionPsi hFieldPsi.
have [beta [c [hC [hBound hDensity]]]] :=
  @bounded_pair_form_functional_exists R h2 n m U hU phi psi hPhi hPsi.
apply: (@weak_exterior_pair_graph_action_iff R h2 n m U hU
  beta phi psi hDensity).2=> v hGraph.
have [K [a [b [hLeft [hRight [hDiv hOff]]]]]] :=
  @current_compact_divergence_graph_tests R h2 n m U hU v hGraph.
have hAction := @current_pair_density_full_test_action R h2 n m U hU
  beta phi psi T S v a b hDensity hTAction hSAction hLeft hRight.
have [rho [hRho hTube]] := @current_compact_closed_tube_inside_exists R n U hU K.
have hSmallIntegral (epsilon : R) (hEpsilon : 0<epsilon) (hSmall : epsilon<rho) :
    is_measure_integral Leb (real_total_integrand (fun x =>
      pairing (tv m a x) (g epsilon x)+
      pairing (tv m.+1 b x) (h epsilon x))) 0%E.
  have hInside : @euclidean_closed_support_tube R n (smooth_compact_carrier K)
      epsilon `<=` U.
    move=> x hx; apply: (@hTube x).
    exact: (@euclidean_closed_support_tube_mono R n (smooth_compact_carrier K)
      (smooth_compact_carrier K) epsilon rho (fun _ hy => hy) (ltW hSmall) x hx).
  have hSmooth := @compact_smooth_convolution_smooth R n (Y m) (YN m) (hYN m)
    (@current_form_complete R h2 n m) (@current_form_separable R h2 n m)
    extensionPhi hFieldPhi (family epsilon) epsilon (g epsilon)
    (@smoothing_dilation_smooth R n kernel hKernel family hFamily epsilon hEpsilon)
    (@smoothing_dilation_zero_beyond_radius R n kernel family
      hKernel hFamily epsilon hEpsilon) (@hG epsilon hEpsilon).
  exact: (@current_smooth_weak_test_on_kernel_locus R h2 n m U hU K a b
    epsilon (g epsilon) (h epsilon) hEpsilon hInside hDiv hOff
    (hSmooth 1%N) (@hEquation epsilon hEpsilon)).
have hError (eta : R) (hEta : 0<eta) : `|T a+S b|<eta.
  have hTwo : 0<(2:R) by rewrite ltr0n.
  have hHalf : 0<eta/2 := divr_gt0 hEta hTwo.
  have [deltaT [hDeltaT hLimitT]] := @current_form_smoothing_test_limit
    R h2 n m kernel family hKernel hFamily extensionPhi T hT hTAction
    g hG a (eta/2) hHalf.
  have [deltaS [hDeltaS hLimitS]] := @current_form_smoothing_test_limit
    R h2 n m.+1 kernel family hKernel hFamily extensionPsi S hS hSAction
    h hH b (eta/2) hHalf.
  pose d := Order.min rho (Order.min deltaT deltaS).
  have hD : 0<d by rewrite /d !lt_min hRho hDeltaT hDeltaS.
  pose epsilon := d/2.
  have hEpsilon : 0<epsilon := divr_gt0 hD hTwo.
  have hLessD : epsilon<d by rewrite /epsilon; lra.
  have hDRho : d<=rho by rewrite /d ge_min lexx.
  have hDInner : d<=Order.min deltaT deltaS by rewrite /d ge_min lexx orbT.
  have hInnerT : Order.min deltaT deltaS<=deltaT by rewrite ge_min lexx.
  have hInnerS : Order.min deltaT deltaS<=deltaS by rewrite ge_min lexx orbT.
  have hDDeltaT : d<=deltaT := le_trans hDInner hInnerT.
  have hDDeltaS : d<=deltaS := le_trans hDInner hInnerS.
  have hERho := lt_le_trans hLessD hDRho.
  have hET := lt_le_trans hLessD hDDeltaT.
  have hES := lt_le_trans hLessD hDDeltaS.
  have [t [hTIntegral hTError]] := @hLimitT epsilon hEpsilon hET.
  have [s [hSIntegral hSError]] := @hLimitS epsilon hEpsilon hES.
  have hSum := @real_total_integral_add R X Leb hLeb
    (fun x => pairing (tv m a x) (g epsilon x))
    (fun x => pairing (tv m.+1 b x) (h epsilon x))
    t s hTIntegral hSIntegral.
  have hZero : t+s=0 := EFin_inj
    (measure_integral_unique hSum (@hSmallIntegral epsilon hEpsilon hERho)).
  have hIdentity : T a+S b=(T a-t)+(S b-s) by lra.
  have hFirst : `|T a-t|<eta/2.
    rewrite distrC; exact: hTError.
  have hSecond : `|S b-s|<eta/2.
    rewrite distrC; exact: hSError.
  have hTriangle := ler_normD (T a-t) (S b-s).
  rewrite -hIdentity in hTriangle.
  lra.
have hZero : T a+S b=0.
  case: (pselect (T a+S b=0))=> hZero; first exact: hZero.
  have hPositive : 0<`|T a+S b|.
    rewrite normr_gt0; apply/eqP; exact: hZero.
  have hStrict := @hError `|T a+S b| hPositive.
  by rewrite ltxx in hStrict.
by rewrite hAction hZero.
Qed.
End SmoothingConverse.
