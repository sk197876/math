(** Federer (1969), 4.1.18, p. 375: the ordinary
    convolution Phi_epsilon*xi of an original Omega
    field is an actual smooth multivector field.
    It represents current smoothing with the explicitly
    reflected kernel. The original kernel-pairing law
    proves this identity without kernel evenness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanLebesgueDimensions Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  AlternatingForms AlternatingPairing CurrentCoefficientNorms CurrentSpaces CurrentVectorSpaces
  CurrentVectorCompleteness CurrentMultivectorDual MultivectorDualSealed ContinuousDualUP
  SmoothTestSpaces SmoothTestEvaluation SmoothingKernelUP SmoothingDilationUP SmoothingDilationSmooth
  SmoothingDilationNonzeroRadius SmoothingKernelReflection SmoothingConvolutionUP SmoothingConvolutionExistence
  CurrentSmoothingOperators CurrentSmoothingSmoothDensity CurrentSmoothLebesgue CurrentDensityUniqueness
  CompactSummableConvolutionKernelPairing CompactSummableMultivectors CompactSummableMultivectorDensity
  CompactSummableMultivectorAmbient CompactSummableFullCurrentAction GloballySummableFieldLocalIntegrability
  TranslatedKernelTestUP TranslatedKernelTestSealed MeasureIntegralUP MeasureIntegralUniqueness
  MeasureIntegralGraphEquivalence SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CompactSummableFullConvolution.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation V:=(exterior_power X m).
Local Notation VN:=(@current_vector_mass R h2 n m).
Local Notation hVN:=(@current_vector_mass_real_norm R h2 n m).
Local Notation VF:=(@current_vector_smooth_space R h2 n Full hFull m).
Local Notation vv:=(@current_vector_smooth_value R h2 n Full hFull m).
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
Local Notation reflectedPhi:=(fun x:X=>phi (-x)).
Local Notation reflectedFamily:=(fun epsilon x=>family epsilon (-x)).
Local Notation hReflectedPhi:=(@smoothing_reflected_kernel_laws R n phi hPhi).
Local Notation hReflectedFamily:=(@smoothing_reflected_dilation_laws R n phi family hFamily).
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation hKernel:=(@smoothing_dilation_smooth R n reflectedPhi hReflectedPhi
  reflectedFamily hReflectedFamily epsilon hEpsilon).
Local Notation hOff:=(@smoothing_dilation_zero_beyond_radius R n reflectedPhi reflectedFamily
  hReflectedPhi hReflectedFamily epsilon hEpsilon).
Local Notation B:=(@TranslatedKernelTest.value R n (A_m X R^o m) NY hNY E ev hE
  (reflectedFamily epsilon) hKernel epsilon hOff).
Local Notation hB:=(@TranslatedKernelTest.laws R n (A_m X R^o m) NY hNY E ev hE
  (reflectedFamily epsilon) hKernel epsilon hOff).

(** Source for [compact_summable_full_convolution_exists]:
    the ordinary smooth field convolution used in
    Federer 4.1.18, pp. 375–376, is the actual
    smooth density of the reflected-kernel current
    smoothing. All exterior degrees and R^0 are retained. *)
Theorem compact_summable_full_convolution_exists (xi:W):
  exists zeta:VF,
    is_smoothing_convolution hVN (family epsilon) (raw xi) (vv zeta) /\
    @current_smooth_lebesgue_map R h2 n m zeta=
      @current_smoothing R h2 n m reflectedPhi reflectedFamily
        hReflectedPhi hReflectedFamily (A xi) epsilon.
Proof.
have hLocal:=@globally_summable_field_locally_integrable R n V VN hVN (raw xi)
  (@compact_summable_multivector_size R h2 n m Full hFull xi)
  (@compact_summable_multivector_ambient_measurable R h2 n m Full hFull xi)
  (@compact_summable_multivector_ambient_integral R h2 n m Full hFull xi).
have[g hConv]:=@smoothing_convolution_exists R n V VN hVN
  (@current_multivector_mass_complete R h2 n m) (@current_multivector_mass_separable R h2 n m)
  phi hPhi family hFamily epsilon hEpsilon (raw xi) hLocal.
have[zeta [hAction hKernelAction]]:=@current_smoothing_smooth_density_exists R h2 n m
  reflectedPhi reflectedFamily hReflectedPhi hReflectedFamily epsilon hEpsilon (A xi).
have hValues (z:X) (theta:A_m X R^o m):pairing (vv zeta z) theta=pairing (g z) theta.
  rewrite (hKernelAction z theta).
  exact:esym (@compact_summable_convolution_kernel_pairing R h2 n m
    phi family hPhi hFamily epsilon hEpsilon xi g hConv z theta).
have hField:vv zeta=g.
  apply:funext=>z.
  apply:(continuous_dual_injective (@current_multivector_continuous_dual R h2 n m)).
  apply:hom_ext=>theta;rewrite !MultivectorDual.laws;exact:hValues.
exists zeta;split;first by rewrite hField.
exact:(@current_density_action_unique R h2 n m (@euclidean_lebesgue_measure R n)
  (vv zeta) (@current_smooth_lebesgue_map R h2 n m zeta)
  (@current_smoothing R h2 n m reflectedPhi reflectedFamily hReflectedPhi hReflectedFamily
    (A xi) epsilon) (current_smooth_lebesgue_action zeta) hAction).
Qed.
End CompactSummableFullConvolution.
