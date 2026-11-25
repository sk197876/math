(** Federer (1969), 4.1.18, p. 375: the
    literal Radon average of the original translated
    variation measures, with weight Phi_epsilon(-z).
    Reuse the independently specified opaque measure
    average; no finite total variation is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentDomain
  CurrentSpaces CurrentIntegrationCriterion NormalisedCurrentSealed NormalisedDistributionRepresentationUP
  DistributionIntegrationRepresentationUP CurrentAmbientVariation CurrentAmbientVariationIntegral
  SmoothingKernelUP SmoothingDilationUP SmoothingConvolutionUP SmoothingReflectedWeight
  EuclideanKernelRadonAverageUP EuclideanKernelRadonAverageSealed EuclideanKernelRadonAverageConvolution
  EuclideanLebesgueDimensions MeasureUP RadonMeasureUP MeasureIntegralUP SummableRealFunctionUP
  RadonCompactScalarIntegral FunctionLatticeUP CompactSupportFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentSmoothingVariationAverage.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation FT:=(current_domain R n Full).
Variable T:@current_space R h2 n Full hFull m.
Hypothesis hT:@is_integration_representable_current R h2 n m Full hFull T.
Local Notation beta:=(@NormalisedCurrent.measure R h2 n m Full hFull T hT).
Local Notation hNorm:=(@NormalisedCurrent.laws R h2 n m Full hFull T hT).
Local Notation hRep:=(normalised_distribution_representation_laws hNorm).
Local Notation hm:=(distribution_representation_measure hRep).
Local Notation hr:=(distribution_representation_radon hRep).
Local Notation B:=(@radon_positive_compact_integral R FT beta hm hr).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation w:=(fun z:X=>family epsilon (-z)).
Local Notation hW:=(norm_class_continuous
  (@smoothing_reflected_weight_smooth R n phi family hPhi hFamily epsilon hEpsilon 0%N)).
Local Notation hPositive:=(@smoothing_reflected_weight_nonnegative R n phi family hPhi hFamily
  epsilon hEpsilon).
Local Notation hOff:=(@smoothing_reflected_weight_off R n phi family hPhi hFamily epsilon hEpsilon).

(** Source for [current_smoothing_variation_average]: the
    literal integral of Phi_epsilon(-z) tau_z#||T||
    in Federer 4.1.18, p. 375. Its original
    positive compact-test specification is exposed below. *)
Definition current_smoothing_variation_average:set XT->\bar R:=
  @EuclideanKernelRadonAverage.value R n beta hm hr w hW hPositive epsilon hOff.
Local Notation nu:=current_smoothing_variation_average.

(** Source for [current_smoothing_variation_average_laws]:
    the original averaged translated variation is
    a Radon measure and has its literal scalar
    translation integral, Federer 4.1.18, p. 375. *)
Theorem current_smoothing_variation_average_laws:
  @is_euclidean_kernel_radon_average R n beta hm hr w nu.
Proof.
exact:(@EuclideanKernelRadonAverage.laws R n beta hm hr w hW hPositive epsilon hOff).
Qed.
Local Notation hNu:=current_smoothing_variation_average_laws.
Local Notation D:=(@radon_positive_compact_integral R XT nu hNu.1 hNu.2.1).

(** Source for [current_smoothing_variation_average_translation]:
    testing the original integral of translated
    variation measures on f gives the literal
    iterated scalar integral, 4.1.18, p. 375. *)
Theorem current_smoothing_variation_average_translation (f:XT->R):
  positive_function_lattice (@compactly_supported_continuous_functions R XT) f ->
  is_measure_integral (@euclidean_lebesgue_measure R n)
    (real_total_integrand (fun z:X=>family epsilon (-z)*B (fun x:FT=>f (set_val x+z))))
    (D f)%:E.
Proof.
move=>hF;have hFormula:=hNu.2.2.
exact:(@hFormula hNu.1 hNu.2.1 f hF).
Qed.

(** Source for [current_smoothing_variation_average_convolution]:
    the averaged measure acts by the original
    scalar convolution on the source variation,
    supporting the displayed inequality in 4.1.18,
    p. 375. The same nonsymmetric kernel is retained. *)
Theorem current_smoothing_variation_average_convolution (f g:XT->R^o):
  positive_function_lattice (@compactly_supported_continuous_functions R XT) f ->
  positive_function_lattice (@compactly_supported_continuous_functions R XT) g ->
  is_smoothing_convolution (@scalar_absolute_value_norm R) (family epsilon) f g ->
  D f= @radon_positive_compact_integral R XT
    (@current_ambient_variation R h2 n m T hT)
    (@current_ambient_variation_laws R h2 n m T hT).1
    (@current_ambient_variation_laws R h2 n m T hT).2 g.
Proof.
move=>hF hG hConv.
rewrite (@current_ambient_variation_positive_compact_value R h2 n m T hT g hG).
exact:(@euclidean_kernel_radon_average_convolution_value R n beta hm hr
  phi family hPhi hFamily epsilon hEpsilon nu hNu f g hF hG hConv).
Qed.
End CurrentSmoothingVariationAverage.
Arguments current_smoothing_variation_average : clear implicits.
