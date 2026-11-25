(** Federer (1969), 4.1.19, p. 377: the
    original weak equation implies d(Phi_epsilon*phi)
    =Phi_epsilon*psi wherever the translated kernel lies
    inside the original open U. The kernel need
    not be even, and no boundary equation is imposed. *)
From mathcomp Require Import boolp all_boot all_order all_algebra
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormDifferentialLocal NormOpenDomainLaws NormRegularity NormClassOneUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanCoordinateForms ExteriorGrading AlternatingForms
  AlternatingPairing CurrentDomain CurrentCoefficientNorms CurrentCoefficientCompleteness
  CurrentVectorSpaces CurrentOneCovectorMap SmoothCurrentDivergence SmoothCompactSet SmoothFunctionSpaceUP
  SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation CurrentCovectorDual
  CompactContinuousVectorZeroExtension FlatCochainRepresentationUP
  BoundedCurrentFormSmoothing CurrentFormFieldDistribution CurrentFormConvolutionDensity
  CurrentKernelTestDivergence CurrentKernelDensityExterior WeakExteriorFullCompactTest
  CurrentWeakExteriorPairUP ClosedBallContainmentOpen FiniteNormEquivalence
  SmoothingKernelUP SmoothingDilationUP SmoothingDilationSmooth
  SmoothingDilationNonzeroRadius SmoothingKernelReflection SmoothingConvolutionUP
  CompactSmoothConvolutionSmoothness CompactScalarKernelDirectional
  TranslatedKernelTestUP TranslatedKernelTestSealed ExteriorDerivativeUP
  EuclideanLebesgueDimensions MeasureIntegralUP MeasureIntegralUniqueness
  SummableRealFunctionUP SummableRealArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section WeakSmoothing.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation V d := (exterior_power X d).
Local Notation VN d := (@current_vector_mass R h2 n d).
Local Notation hVN d := (@current_vector_mass_real_norm R h2 n d).
Local Notation Y d := (A_m X R^o d).
Local Notation YN d := (@current_form_comass R h2 n d).
Local Notation hYN d := (@current_form_comass_real_norm R h2 n d).
Local Notation ed d := (@current_covector_evaluation R n d).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation E d := (@current_vector_smooth_space R h2 n Full hFull d).
Local Notation ev d := (@current_vector_smooth_value R h2 n Full hFull d).
Local Notation hE d := (@current_vector_smooth_space_laws R h2 n Full hFull d).
Local Notation DT d := (smooth_test_space (hE d)).
Local Notation cut j := (@current_one_covector_map R h2 n m (euclidean_coordinate_form j)).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation hLeb := (euclidean_lebesgue_is_measure R n).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation UT := (current_domain R n U).
Variables (phi : UT -> Y m) (psi : UT -> Y m.+1).
Local Notation extensionPhi := (@compact_vector_open_extension R XT U (Y m) phi).
Local Notation extensionPsi := (@compact_vector_open_extension R XT U (Y m.+1) psi).
Variables (kernel : X -> R) (family : R -> X -> R).
Hypothesis hKernel : is_smoothing_kernel kernel.
Hypothesis hFamily : is_smoothing_dilation kernel family.
Variable epsilon : R.
Hypothesis hEpsilon : 0<epsilon.
Local Notation refKernel := (fun x : X => kernel (-x)).
Local Notation refFamily := (fun e x => family e (-x)).
Local Notation hRefKernel := (@smoothing_reflected_kernel_laws R n kernel hKernel).
Local Notation hRefFamily :=
  (@smoothing_reflected_dilation_laws R n kernel family hFamily).
Local Notation rho := (refFamily epsilon).
Local Notation hRho := (@smoothing_dilation_smooth R n refKernel hRefKernel
  refFamily hRefFamily epsilon hEpsilon).
Local Notation hRhoOff := (@smoothing_dilation_zero_beyond_radius R n refKernel
  refFamily hRefKernel hRefFamily epsilon hEpsilon).
Local Notation B d := (@TranslatedKernelTest.value R n (V d) (VN d) (hVN d)
  (E d) (ev d) (hE d) rho hRho epsilon hRhoOff).
Local Notation hB d := (@TranslatedKernelTest.laws R n (V d) (VN d) (hVN d)
  (E d) (ev d) (hE d) rho hRho epsilon hRhoOff).

(** Source for [current_weak_exterior_smoothing]: the
    forward smoothing assertion of Federer 4.1.19,
    p. 377, at every positive original
    radius and every centre whose closed kernel
    ball lies in U. Both convolutions are the
    actual vector integrals of the original fields;
    zero extension is only their ambient presentation. *)
Theorem current_weak_exterior_smoothing
    (g : X -> Y m) (h : X -> Y m.+1) :
  @is_bounded_measurable_current_form R h2 n U m phi ->
  @is_bounded_measurable_current_form R h2 n U m.+1 psi ->
  @is_weak_current_exterior_pair R h2 n m U hU phi psi ->
  is_smoothing_convolution (hYN m) (family epsilon) extensionPhi g ->
  is_smoothing_convolution (hYN m.+1) (family epsilon) extensionPsi h ->
  forall z, norm_closed_ball_containment U epsilon z ->
    has_exterior_derivative NX (YN m) U g z (h z).
Proof.
move=> hPhi hPsi hWeak hGConv hHConv z hCentre.
have hFieldPhi := @bounded_current_form_extension_locally_integrable
  R h2 n m U hU phi hPhi.
have hFieldPsi := @bounded_current_form_extension_locally_integrable
  R h2 n m.+1 U hU psi hPsi.
have [T [hT hTAction]] :=
  @current_form_field_distribution_exists R h2 n m extensionPhi hFieldPhi.
have [S [hS hSAction]] :=
  @current_form_field_distribution_exists R h2 n m.+1 extensionPsi hFieldPsi.
have hDensity := @current_form_convolution_density R h2 n m kernel family hKernel hFamily
  epsilon hEpsilon extensionPhi g T hTAction hGConv.
have hDensityP := @current_form_convolution_density R h2 n m.+1 kernel family hKernel hFamily
  epsilon hEpsilon extensionPsi h S hSAction hHConv.
have hSmoothG := @compact_smooth_convolution_smooth R n (Y m) (YN m) (hYN m)
  (@current_form_complete R h2 n m) (@current_form_separable R h2 n m)
  extensionPhi hFieldPhi (family epsilon) epsilon g
  (@smoothing_dilation_smooth R n kernel hKernel family hFamily epsilon hEpsilon)
  (@smoothing_dilation_zero_beyond_radius R n kernel family hKernel hFamily
    epsilon hEpsilon) hGConv.
have hDirections (j : 'I_n) := @compact_scalar_kernel_directional_exists R n rho epsilon
  (@coordinate_basis R n j) hRho hRhoOff.
have [theta hTheta] := choice hDirections.
have [G hG] := choice hTheta.
pose C j := @TranslatedKernelTest.value R n (V m) (VN m) (hVN m)
  (E m) (ev m) (hE m) (theta j) (hG j).1 epsilon (hG j).2.1.
have hC j := @TranslatedKernelTest.laws R n (V m) (VN m) (hVN m)
  (E m) (ev m) (hE m) (theta j) (hG j).1 epsilon (hG j).2.1.
have hBallInside : [set x : X | NX (x-z)<=epsilon] `<=` U.
  move=> x hx; apply: hCentre.
  by rewrite (real_seminorm_subtract hNX.1).
pose K := @Build_smooth_compact_set R X NX hNX U
  [set x | NX (x-z)<=epsilon] hBallInside
  (@finite_norm_closed_ball_compact R X n (@coordinate_basis R n)
    (@coordinate_basisP R n) NX hNX z epsilon).
pose KF := @Build_smooth_compact_set R X NX hNX Full
  [set x | NX (x-z)<=epsilon] (fun _ _ => Logic.I)
  (@finite_norm_closed_ball_compact R X n (@coordinate_basis R n)
    (@coordinate_basisP R n) NX hNX z epsilon).
have hAnn (a : V m.+1) :
    (\sum_(j : 'I_n) T (C j z (cut j a)))+S (B m.+1 z a)=0.
  pose eta := smooth_test_inclusion (hE m.+1) (B m.+1 z a).
  have hSupport : @smooth_function_support R X (V m.+1) NX hNX Full
      (E m.+1) (ev m.+1) eta `<=` smooth_compact_carrier KF.
    apply: (smooth_function_compact_support_iff (hE m.+1) KF eta).2=> x hx.
    change (smooth_test_value (hE m.+1) (B m.+1 z a) x=0).
    rewrite (@hB m.+1 z a x).
    have hFar : epsilon<NX (x-z).
      rewrite ltNge; apply/negP=> hxNear; exact: (hx hxNear).
    by rewrite (@hRhoOff (x-z) hFar) scale0r.
  have hWeakFull := @weak_current_exterior_full_compact_test R h2 n m U hU
    phi psi K eta hWeak hSupport.
  pose test := \sum_(j : 'I_n) C j z (cut j a).
  have hFirst := hTAction test.
  have hSecond := hSAction (B m.+1 z a).
  have hSum := @real_total_integral_add R X Leb hLeb
    (fun x => ed m (extensionPhi x) (smooth_test_value (hE m) test x))
    (fun x => ed m.+1 (extensionPsi x) (smooth_test_value (hE m.+1) (B m.+1 z a) x))
    (T test) (S (B m.+1 z a)) hFirst hSecond.
  have hIntegrands : (fun x =>
        ed m (extensionPhi x) (smooth_test_value (hE m) test x)+
        ed m.+1 (extensionPsi x) (smooth_test_value (hE m.+1) (B m.+1 z a) x))=
      (fun x => pairing
        (ev m (@smooth_current_divergence R h2 n m Full hFull eta) x) (extensionPhi x)+
        pairing (ev m.+1 eta x) (extensionPsi x)).
    apply: funext=> x.
    have hDiv := @current_kernel_test_divergence_values R h2 n m rho hRho
      theta G (fun j => (hG j).2.2.1) (fun j => (hG j).2.2.2)
      (B m.+1) C (hB m.+1) hC z a x.
    change (pairing (smooth_test_value (hE m) test x) (extensionPhi x)+
      pairing (ev m.+1 eta x) (extensionPsi x)=
      pairing (ev m (@smooth_current_divergence R h2 n m Full hFull eta) x)
        (extensionPhi x)+pairing (ev m.+1 eta x) (extensionPsi x)).
    by rewrite hDiv.
  rewrite hIntegrands in hSum.
  have hZero := EFin_inj (measure_integral_unique hSum hWeakFull).
  by rewrite /test linear_sum in hZero.
have hFullDerivative := @current_kernel_density_exterior_from_tests R h2 n m
  rho hRho epsilon hRhoOff theta G (fun j => (hG j).1) (fun j => (hG j).2.1)
  (fun j => (hG j).2.2.1) (fun j => (hG j).2.2.2)
  (B m) (B m.+1) C (hB m) hC T hT S g h hDensity hDensityP z
  (hSmoothG 1%N) hAnn.
have hZ : U z.
  apply: hCentre; rewrite subrr (real_seminorm_zero hNX.1); exact: ltW hEpsilon.
have [L [hL hExterior]] := hFullDerivative.
exists L; split; last exact: hExterior.
exact: (@norm_differential_restrict R X (Y m) NX (YN m) Full U g z L
  (fun _ _ => Logic.I) (@hU z hZ) hL).
Qed.
End WeakSmoothing.
