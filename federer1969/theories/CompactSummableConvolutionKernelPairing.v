(** Federer (1969), 4.1.18, pp. 375–377:
    each ordinary convolution coefficient is exactly
    the original density current evaluated on the
    translated reflected-kernel test. This literal
    formula retains arbitrary nonsymmetric kernels
    for the final smoothing graph argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanLebesgueDimensions Hom Bilinear RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  AlternatingForms AlternatingPairing CurrentSpaces CurrentCoefficientNorms
  SmoothTestSpaces SmoothTestEvaluation SmoothingKernelUP SmoothingDilationUP SmoothingDilationSmooth
  SmoothingDilationNonzeroRadius SmoothingKernelReflection SmoothingConvolutionUP
  CurrentVectorIntegralPairing CompactSummableMultivectors CompactSummableMultivectorDensity
  CompactSummableMultivectorAmbient CompactSummableFullCurrentAction
  TranslatedKernelTestUP TranslatedKernelTestSealed MeasureIntegralUP MeasureIntegralUniqueness
  SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section KernelPairing.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation V:=(exterior_power X m).
Local Notation hVN:=(@current_vector_mass_real_norm R h2 n m).
Local Notation E:=(@current_smooth_space R h2 n Full hFull m).
Local Notation ev:=(@current_smooth_value R h2 n Full hFull m).
Local Notation hE:=(@current_smooth_space_laws R h2 n Full hFull m).
Local Notation NY:=(@current_form_comass R h2 n m).
Local Notation hNY:=(@current_form_comass_real_norm R h2 n m).
Local Notation W:=(@compact_summable_multivector_space R h2 n m Full hFull).
Local Notation A:=(@compact_summable_multivector_current R h2 n m Full hFull).
Local Notation raw:=(@compact_summable_multivector_ambient_value R h2 n m Full hFull).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation hKernel:=(@smoothing_dilation_smooth R n (fun x:X=>phi (-x))
  (@smoothing_reflected_kernel_laws R n phi hPhi)
  (fun e x=>family e (-x))
  (@smoothing_reflected_dilation_laws R n phi family hFamily) epsilon hEpsilon).
Local Notation hOff:=(@smoothing_dilation_zero_beyond_radius R n
  (fun x:X=>phi (-x)) (fun e x=>family e (-x))
  (@smoothing_reflected_kernel_laws R n phi hPhi)
  (@smoothing_reflected_dilation_laws R n phi family hFamily) epsilon hEpsilon).
Local Notation B:=(@TranslatedKernelTest.value R n (A_m X R^o m) NY hNY E ev hE
  (fun x=>family epsilon (-x)) hKernel epsilon hOff).
Local Notation hB:=(@TranslatedKernelTest.laws R n (A_m X R^o m) NY hNY E ev hE
  (fun x=>family epsilon (-x)) hKernel epsilon hOff).

(** Source for [compact_summable_convolution_kernel_pairing]:
    the exact translated-kernel test action for the
    original ordinary convolutions in 4.1.18,
    pp. 375–377. The formula is pointwise
    at every z and every covector theta. *)
Theorem compact_summable_convolution_kernel_pairing (xi:W) (g:X->V):
  is_smoothing_convolution hVN (family epsilon) (raw xi) g ->
  forall z theta,pairing (g z) theta=
    @current_value R h2 n Full hFull m (A xi) (B z theta).
Proof.
move=>hConv z theta.
have hOriginal:=@compact_summable_full_current_action R h2 n m xi (B z theta).
have hScalar:=@current_vector_integral_pairing R h2 n m X
  (@euclidean_lebesgue_measure R n)
  (fun x=>family epsilon (z-x)*:raw xi x) (g z) theta (hConv z).
have hFunction:(fun x:X=>pairing (raw xi x)
      (@current_test_value R h2 n Full hFull m (B z theta) x))=
    (fun x:X=>pairing (family epsilon (z-x)*:raw xi x) theta).
  apply:funext=>x.
  have hValue:=hB z theta x.
  change (@current_test_value R h2 n Full hFull m (B z theta) x=
    family epsilon (-(x-z))*:theta) in hValue.
  rewrite hValue.
  change (pairing (raw xi x) (family epsilon (-(x-z))*:theta)=
    pairing (family epsilon (z-x)*:raw xi x) theta).
  by rewrite opprB (bilZr (@pairing_bilinear R X R^o m))
    (bilZl (@pairing_bilinear R X R^o m)).
rewrite hFunction in hOriginal.
exact:(EFin_inj (measure_integral_unique hScalar hOriginal)).
Qed.
End KernelPairing.
