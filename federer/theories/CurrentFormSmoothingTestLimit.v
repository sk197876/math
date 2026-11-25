(** Federer (1969), 4.1.19, p. 377: the
    ordinary convolutions of measurable forms converge in
    every original compact smooth test action. Reuse the
    literal test-smoothing limit of 4.1.2, p. 347,
    and its integral representation, keeping kernel reflection explicit. *)
From mathcomp Require Import boolp all_boot all_order all_algebra
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingForms AlternatingPairing CurrentCoefficientNorms
  CurrentVectorSpaces CurrentVectorCompleteness CurrentCovectorDual ContinuousDualUP
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestSpaces SmoothTestTopology
  SmoothTestEvaluation SmoothSmoothingFamilyUP SmoothSmoothingFamilySealed
  TestSmoothingFamilyUP TestSmoothingFamilySealed SmoothingKernelUP SmoothingDilationUP
  SmoothingDilationSmooth SmoothingDilationNonzeroRadius SmoothingKernelReflection
  SmoothingConvolutionUP TranslatedKernelTestUP TranslatedKernelTestSealed
  DistributionIntegralFieldUP NormOpenTopology OpenFamilyTopologyUP
  CurrentFormConvolutionDensity SmoothedDistributionExistence
  DistributionSmoothingTestLimit EuclideanLebesgueDimensions
  MeasureIntegralUP SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section FormSmoothingTestLimit.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n d : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation V := (exterior_power X d).
Local Notation VN := (@current_vector_mass R h2 n d).
Local Notation hVN := (@current_vector_mass_real_norm R h2 n d).
Local Notation Y := (A_m X R^o d).
Local Notation YN := (@current_form_comass R h2 n d).
Local Notation hYN := (@current_form_comass_real_norm R h2 n d).
Local Notation ed := (@current_covector_evaluation R n d).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation E := (@current_vector_smooth_space R h2 n Full hFull d).
Local Notation ev := (@current_vector_smooth_value R h2 n Full hFull d).
Local Notation hE := (@current_vector_smooth_space_laws R h2 n Full hFull d).
Local Notation D := (@current_vector_smooth_derivatives R h2 n Full hFull d).
Local Notation hD := (@current_vector_smooth_derivative_laws R h2 n Full hFull d).
Local Notation DT := (smooth_test_space hE).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Variables (kernel : X -> R) (family : R -> X -> R).
Hypothesis hKernel : is_smoothing_kernel kernel.
Hypothesis hFamily : is_smoothing_dilation kernel family.
Local Notation refKernel := (fun x : X => kernel (-x)).
Local Notation refFamily := (fun e x => family e (-x)).
Local Notation hRefKernel := (@smoothing_reflected_kernel_laws R n kernel hKernel).
Local Notation hRefFamily :=
  (@smoothing_reflected_dilation_laws R n kernel family hFamily).
Local Notation P := (@SmoothSmoothingFamily.value R n V VN hVN
  (@current_multivector_mass_complete R h2 n d)
  (@current_multivector_mass_separable R h2 n d)
  E ev hE refKernel hRefKernel refFamily hRefFamily).
Local Notation hP := (@SmoothSmoothingFamily.laws R n V VN hVN
  (@current_multivector_mass_complete R h2 n d)
  (@current_multivector_mass_separable R h2 n d)
  E ev hE refKernel hRefKernel refFamily hRefFamily).

(** Source for [current_form_transpose_test_smoothing]:
    the reflected original test smoothing transposed
    by ordinary coefficient convolution in Federer
    4.1.19, p. 377. This is
    the old opaque test operator, with no
    even-kernel convention or new test space. *)
Definition current_form_transpose_test_smoothing : R -> Hom DT DT :=
  @TestSmoothingFamily.value R n V VN hVN E ev hE refKernel hRefKernel
    refFamily hRefFamily P hP.
Local Notation Q := current_form_transpose_test_smoothing.

(** Source for [current_form_transpose_test_smoothing_laws]:
    exact agreement with the original reflected
    smooth convolution after inclusion of tests,
    supporting Federer 4.1.19, p. 377. *)
Lemma current_form_transpose_test_smoothing_laws :
  @is_test_smoothing_family R X V NX VN hNX hVN Full E ev hE P Q.
Proof. exact: TestSmoothingFamily.laws. Qed.
Local Notation hQ := current_form_transpose_test_smoothing_laws.

Variable f : X -> Y.
Variable T : Hom DT R^o.
Hypothesis hT : open_family_continuous (smooth_test_opens hE hD)
  (norm_open_family (@scalar_absolute_value_norm R)) T.
Hypothesis hAction : is_distribution_integral_action Leb ed f (smooth_test_value hE) T.

(** Source for [current_form_smoothing_test_action]:
    the exact scalar pairing of an ordinary
    form convolution and a compact smooth test,
    used in the smoothing criterion of Federer
    4.1.19, p. 377. The old
    smoothed distribution integral proves the interchange. *)
Theorem current_form_smoothing_test_action epsilon (hEpsilon : 0<epsilon)
    (g : X -> Y) :
  is_smoothing_convolution hYN (family epsilon) f g ->
  forall a : DT, is_measure_integral Leb (real_total_integrand
    (fun x => pairing (smooth_test_value hE a x) (g x))) (T (Q epsilon a))%:E.
Proof.
move=> hConv a.
pose hSmooth := @smoothing_dilation_smooth R n refKernel hRefKernel
  refFamily hRefFamily epsilon hEpsilon.
pose hOff := @smoothing_dilation_zero_beyond_radius R n refKernel refFamily
  hRefKernel hRefFamily epsilon hEpsilon.
pose B := @TranslatedKernelTest.value R n V VN hVN E ev hE
  (refFamily epsilon) hSmooth epsilon hOff.
have hB := @TranslatedKernelTest.laws R n V VN hVN E ev hE
  (refFamily epsilon) hSmooth epsilon hOff.
have hG := @current_form_convolution_density R h2 n d kernel family hKernel hFamily
  epsilon hEpsilon f g T hAction hConv.
have [A [hA [xi [hXiSmooth [hXi hXiAction]]]]] :=
  @smoothed_distribution_exists_with_density R n V VN hVN
    (@current_multivector_mass_complete R h2 n d)
    (@current_multivector_mass_separable R h2 n d)
    E ev hE D hD (refFamily epsilon) hSmooth epsilon hOff (ltW hEpsilon)
    B hB (P epsilon) (@hP epsilon hEpsilon) (Q epsilon) (@hQ epsilon hEpsilon)
    T hT Y ed YN (@current_covector_continuous_dual R h2 n d).
have hSame : xi=g.
  apply: funext=> x; apply: (continuous_dual_injective
    (@current_covector_continuous_dual R h2 n d)).
  apply: hom_ext=> v; exact: (eq_trans (hXi x v) (esym (hG x v))).
have hIntegral := hXiAction a.
rewrite hSame (@hA a) in hIntegral.
exact: hIntegral.
Qed.

(** Source for [current_form_smoothing_test_limit]:
    every original compact test pairing of
    Phi_epsilon*phi tends to the original pairing,
    supporting the converse smoothing implication in
    Federer 4.1.19, p. 377.
    The original form may be discontinuous and U
    may have infinite Lebesgue measure. *)
Theorem current_form_smoothing_test_limit (g : R -> X -> Y) :
  (forall epsilon, 0<epsilon ->
    is_smoothing_convolution hYN (family epsilon) f (g epsilon)) ->
  forall (a : DT) (eta : R), 0<eta ->
  exists delta : R, 0<delta /\ forall epsilon, 0<epsilon -> epsilon<delta ->
    exists b : R, is_measure_integral Leb (real_total_integrand
      (fun x => pairing (smooth_test_value hE a x) (g epsilon x))) b%:E /\
      `|b-T a|<eta.
Proof.
move=> hConv a eta hEta.
have [delta [hDelta hLimit]] := @distribution_smoothing_test_limit R n V VN hVN
  (@current_multivector_mass_complete R h2 n d)
  (@current_multivector_mass_separable R h2 n d)
  E ev hE D hD refKernel hRefKernel refFamily hRefFamily P hP Q hQ
  T hT a eta hEta.
exists delta; split; first exact: hDelta.
move=> epsilon hEpsilon hSmall.
exists (T (Q epsilon a)); split; last exact: (@hLimit epsilon hEpsilon hSmall).
exact: (@current_form_smoothing_test_action epsilon hEpsilon
  (g epsilon) (@hConv epsilon hEpsilon) a).
Qed.
End FormSmoothingTestLimit.
