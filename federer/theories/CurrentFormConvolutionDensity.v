(** Federer (1969), 4.1.19, p. 377: the
    ordinary convolution of a form field is precisely
    the kernel density of its original distribution,
    using the reflected kernel in the translated-test
    convention of 4.1.2, p. 347. *)
From mathcomp Require Import boolp all_boot all_order all_algebra
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingForms AlternatingPairing CurrentCoefficientNorms
  CurrentVectorSpaces CurrentCovectorDual CurrentFormIntegralPairing
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation
  SmoothingKernelUP SmoothingDilationUP SmoothingDilationSmooth
  SmoothingDilationNonzeroRadius SmoothingKernelReflection SmoothingConvolutionUP
  TranslatedKernelTestUP TranslatedKernelTestSealed SmoothedDistributionDensityUP
  DistributionIntegralFieldUP EuclideanLebesgueDimensions MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section FormConvolutionDensity.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n d : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation V := (exterior_power X d).
Local Notation VN := (@current_vector_mass R h2 n d).
Local Notation hVN := (@current_vector_mass_real_norm R h2 n d).
Local Notation Y := (A_m X R^o d).
Local Notation NY := (@current_form_comass R h2 n d).
Local Notation hNY := (@current_form_comass_real_norm R h2 n d).
Local Notation E := (@current_vector_smooth_space R h2 n Full hFull d).
Local Notation ev := (@current_vector_smooth_value R h2 n Full hFull d).
Local Notation hE := (@current_vector_smooth_space_laws R h2 n Full hFull d).
Local Notation ed := (@current_covector_evaluation R n d).
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
Local Notation hSmooth :=
  (@smoothing_dilation_smooth R n refKernel hRefKernel refFamily hRefFamily
    epsilon hEpsilon).
Local Notation hOff :=
  (@smoothing_dilation_zero_beyond_radius R n refKernel refFamily
    hRefKernel hRefFamily epsilon hEpsilon).
Local Notation B := (@TranslatedKernelTest.value R n V VN hVN E ev hE
  (refFamily epsilon) hSmooth epsilon hOff).

(** Source for [current_form_convolution_density]: the
    actual Phi_epsilon*phi in Federer 4.1.19,
    p. 377, has exactly the reflected
    translated-kernel pairings with the original field
    distribution. Every actual convolution representative
    is admitted; no kernel symmetry is assumed. *)
Theorem current_form_convolution_density (f g : X -> Y)
    (T : Hom (smooth_test_space hE) R^o) :
  is_distribution_integral_action (@euclidean_lebesgue_measure R n)
    ed f (smooth_test_value hE) T ->
  is_smoothing_convolution hNY (family epsilon) f g ->
  is_smoothed_distribution_density B T ed g.
Proof.
move=> hAction hConv z theta.
have hB := @TranslatedKernelTest.laws R n V VN hVN E ev hE
  (refFamily epsilon) hSmooth epsilon hOff.
have hOriginal := hAction (B z theta).
have hScalar := @current_form_integral_pairing R h2 n d X
  (@euclidean_lebesgue_measure R n)
  (fun x => family epsilon (z-x)*:f x) (g z) theta (hConv z).
have hFunction : (fun x => ed (f x) (smooth_test_value hE (B z theta) x))=
    (fun x => pairing theta (family epsilon (z-x)*:f x)).
  apply: funext=> x; rewrite (hB z theta x).
  change (pairing (family epsilon (-(x-z))*:theta) (f x)=
    pairing theta (family epsilon (z-x)*:f x)).
  by rewrite opprB (bilZl (@pairing_bilinear R X R^o d))
    (bilZr (@pairing_bilinear R X R^o d)).
rewrite hFunction in hOriginal.
change (pairing theta (g z)=T (B z theta)).
exact: (EFin_inj (measure_integral_unique hScalar hOriginal)).
Qed.
End FormConvolutionDensity.
