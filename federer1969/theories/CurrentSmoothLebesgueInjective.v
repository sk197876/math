(** Federer (1969), 4.1.18, p. 377: exact
    smooth-field equality in the original graph
    argument follows from the old kernel
    test action and continuous convolution limit.
    This uses no new passage from an
    almost-everywhere equality to pointwise equality. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms
  AlternatingPairing CurrentSpaces CurrentEvaluation CurrentCoefficientNorms
  CurrentVectorSpaces CurrentVectorCompleteness CurrentMultivectorDual MultivectorDualSealed
  ContinuousDualUP CurrentSmoothLebesgue CurrentDensityAction
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothTestSpaces SmoothTestEvaluation SmoothCompactSet
  SmoothingKernelUP SmoothingKernelSealed SmoothingDilationUP SmoothingDilationSealed
  SmoothingDilationSmooth SmoothingDilationNonzeroRadius SmoothingKernelReflection
  SmoothingConvolutionUP ContinuousCompactConvolution ContinuousSmoothingLocallyUniform
  TranslatedKernelTestUP TranslatedKernelTestSealed CurrentVectorIntegralPairing
  EuclideanLebesgueDimensions MeasureIntegralUP MeasureIntegralUniqueness
  SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SmoothLebesgueInjective.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) =>
  @norm_full_domain_interior R X NX x).
Local Notation V := (exterior_power X m).
Local Notation VN := (@current_vector_mass R h2 n m).
Local Notation hVN := (@current_vector_mass_real_norm R h2 n m).
Local Notation F := (@current_vector_smooth_space R h2 n Full hFull m).
Local Notation fv := (@current_vector_smooth_value R h2 n Full hFull m).
Local Notation hF := (@current_vector_smooth_space_laws R h2 n Full hFull m).
Local Notation Y := (A_m X R^o m).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Local Notation E := (@current_smooth_space R h2 n Full hFull m).
Local Notation ev := (@current_smooth_value R h2 n Full hFull m).
Local Notation hE := (@current_smooth_space_laws R h2 n Full hFull m).
Local Notation L := (@current_smooth_lebesgue_map R h2 n m).
Local Notation action := (@current_value R h2 n Full hFull m).

(** Source for [current_smooth_lebesgue_convolution_zero]:
    if the actual smooth density current
    is zero, each ordinary convolution of
    its original field is pointwise zero,
    supporting Federer 4.1.18, p. 377.
    Reflected translated kernels retain the literal
    ordinary convolution without a symmetry assumption. *)
Theorem current_smooth_lebesgue_convolution_zero (f : F)
    (phi : X -> R) (family : R -> X -> R)
    (hPhi : is_smoothing_kernel phi) (hFamily : is_smoothing_dilation phi family)
    (epsilon : R) (hEpsilon : 0 < epsilon) (g : X -> V) :
  L f=0 -> is_smoothing_convolution hVN (family epsilon) (fv f) g ->
  forall z, g z=0.
Proof.
move=> hZero hConv z.
pose hKernel := @smoothing_dilation_smooth R n (fun x : X => phi (-x))
  (@smoothing_reflected_kernel_laws R n phi hPhi)
  (fun e x => family e (-x))
  (@smoothing_reflected_dilation_laws R n phi family hFamily) epsilon hEpsilon.
pose hOff := @smoothing_dilation_zero_beyond_radius R n (fun x : X => phi (-x))
  (fun e x => family e (-x)) (@smoothing_reflected_kernel_laws R n phi hPhi)
  (@smoothing_reflected_dilation_laws R n phi family hFamily) epsilon hEpsilon.
pose B := @TranslatedKernelTest.value R n Y NY hNY E ev hE
  (fun x => family epsilon (-x)) hKernel epsilon hOff.
have hB := @TranslatedKernelTest.laws R n Y NY hNY E ev hE
  (fun x => family epsilon (-x)) hKernel epsilon hOff.
apply: (continuous_dual_injective (@current_multivector_continuous_dual R h2 n m)).
apply: hom_ext=> theta.
have hZeroEvaluation : @MultivectorDual.evaluation R X m (0 : V) theta=0.
  by rewrite linear0 hom_zeroE.
rewrite hZeroEvaluation MultivectorDual.laws.
have hOriginal := @current_smooth_lebesgue_action R h2 n m f (B z theta).
have hScalar := @current_vector_integral_pairing R h2 n m X
  (@euclidean_lebesgue_measure R n)
  (fun x => family epsilon (z-x)*:fv f x) (g z) theta (hConv z).
have hFunction : (fun x => pairing (fv f x)
    (@current_test_value R h2 n Full hFull m (B z theta) x))=
    (fun x => pairing (family epsilon (z-x)*:fv f x) theta).
  apply: funext=> x.
  have hValue := @hB z theta x.
  change (@current_test_value R h2 n Full hFull m (B z theta) x=
    family epsilon (-(x-z))*:theta) in hValue.
  rewrite hValue.
  change (pairing (fv f x) (family epsilon (-(x-z))*:theta)=
    pairing (family epsilon (z-x)*:fv f x) theta).
  by rewrite opprB (bilZr (@pairing_bilinear R X R^o m))
    (bilZl (@pairing_bilinear R X R^o m)).
have hZeroAction : action (L f) (B z theta)=0.
  by rewrite hZero linear0 hom_zeroE.
change (is_measure_integral (@euclidean_lebesgue_measure R n)
  (real_total_integrand (fun x => pairing (fv f x)
    (@current_test_value R h2 n Full hFull m (B z theta) x)))
  (action (L f) (B z theta))%:E) in hOriginal.
rewrite hFunction hZeroAction in hOriginal.
exact: (EFin_inj (measure_integral_unique hScalar hOriginal)).
Qed.

(** Source for [current_smooth_lebesgue_zero_field]:
    a zero actual smooth density current
    has zero original field at every
    point, supporting the graph equality in
    Federer 4.1.18, p. 377.
    The existing continuous smoothing limit is
    applied on the original singleton compact index. *)
Theorem current_smooth_lebesgue_zero_field (f : F) :
  L f=0 -> forall x, fv f x=0.
Proof.
move=> hZero.
pose phi := @SmoothingKernel.value R n.
pose hPhi := @SmoothingKernel.laws R n.
pose family := @SmoothingDilation.value R n phi.
pose hFamily := @SmoothingDilation.laws R n phi.
have hContinuous := norm_class_continuous (smooth_function_evaluation_smooth hF f 0%N).
have hEach e : exists g : X -> V, 0 < e ->
    is_smoothing_convolution hVN (family e) (fv f) g.
  case: (pselect (0 < e))=> hE.
  - have [g hG] := @continuous_compact_convolution_exists R n V VN hVN
      (@current_multivector_mass_complete R h2 n m) (fv f) hContinuous
      (family e) (@smoothing_dilation_smooth R n phi hPhi family hFamily e hE) e
      (@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily e hE).
    by exists g.
  - exists (fun _ => 0); move=> h; exact: False_ind _ (hE h).
have [g hG] := choice hEach.
move=> x; apply: contrapT=> hNonzero.
have hPositive : 0 < VN (fv f x).
  rewrite (real_norm_positive hVN.1 hVN.2).
  exact/eqP.
pose K := @smooth_compact_singleton R X NX hNX Full x Logic.I.
have [d [hD hNear]] := @continuous_smoothing_locally_uniform R n V VN hVN
  (@current_multivector_mass_complete R h2 n m) phi hPhi family hFamily
  (fv f) g hG hContinuous K (VN (fv f x)) hPositive.
have hHalf : 0 < d/2 by rewrite divr_gt0 // ltr0n.
have hSmall : d/2 < d by lra.
have hEstimate := @hNear (d/2) hHalf hSmall x (erefl x).
have hGZero := @current_smooth_lebesgue_convolution_zero f phi family hPhi
  hFamily (d/2) hHalf (g (d/2)) hZero (@hG (d/2) hHalf) x.
by rewrite hGZero sub0r (real_seminorm_negate hVN.1) ltxx in hEstimate.
Qed.

(** Source for [current_smooth_lebesgue_map_injective]:
    equality of actual smooth density currents
    gives equality of their original smooth
    fields, supporting the exact smoothing verification
    in Federer 4.1.18, p. 377.
    This follows through the preceding kernel-test
    and continuous-limit laws, not an AE representative assertion. *)
Theorem current_smooth_lebesgue_map_injective : injective L.
Proof.
move=> f g hEqual.
have hZero : L (f-g)%R=0.
  by rewrite (linB (hom_linear L)) hEqual subrr.
have hFields := current_smooth_lebesgue_zero_field hZero.
apply: (smooth_function_evaluation_injective hF).
apply: funext=> x.
have hValue := hFields x.
change (smooth_function_values_hom hF (f-g)%R x=0) in hValue.
rewrite (linB (hom_linear (smooth_function_values_hom hF))) in hValue.
by apply/eqP; rewrite -subr_eq0; apply/eqP.
Qed.
End SmoothLebesgueInjective.
