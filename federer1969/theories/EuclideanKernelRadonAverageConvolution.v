(** Federer (1969), 4.1.18, p. 375: integrate
    a positive compact test against the original
    translated variation average by convolving the
    test and then integrating against the original
    variation. The two orders of 2.6.2 prove
    the identity with the reflected weight retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormClassOneUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentDomain
  EuclideanLebesgueDimensions EuclideanFullDomainMeasure EuclideanFullDomainCompactFunctions CurrentDomainRadonSigmaFinite
  SmoothingKernelUP SmoothingDilationUP SmoothingDilationSmooth SmoothingConvolutionUP
  SmoothingReflectedWeight SmoothingReflectedTranslationIntegral ScalarVectorIntegralIdentification
  PartialFunctionUP PartialFunctionBasic PartialProductSections ParameterizedIntegral
  MeasureUP MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  SummableRealFunctionUP ProductMeasure ProductFunctionFubini CountablyMeasurableFunctions
  CountablyMeasurableProduct CountablyMeasurableNullModification ExtendedRealOrderTopology
  RadonMeasureUP RadonCompactScalarIntegral FunctionLatticeUP CompactSupportFunctionUP
  EuclideanKernelRadonAverageUP EuclideanKernelRadonAverageProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section EuclideanKernelRadonAverageConvolution.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation FT:=(current_domain R n Full).
Local Notation PT:=(Choice.clone (FT*FT)%type _).
Local Notation alpha:=(@euclidean_full_domain_measure R n).
Local Notation hAlpha:=(@euclidean_full_domain_measure_laws R n).1.
Local Notation hAlphaRadon:=(@euclidean_full_domain_measure_laws R n).2.
Variable beta:set FT->\bar R.
Hypotheses (hBeta:is_measure beta) (hBetaRadon:is_radon_measure beta).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation w:=(fun z:X=>family epsilon (-z)).
Variable nu:set XT->\bar R.
Hypothesis hNu:@is_euclidean_kernel_radon_average R n beta hBeta hBetaRadon w nu.
Local Notation D:=(@radon_positive_compact_integral R XT nu hNu.1 hNu.2.1).

(** Source for [euclidean_kernel_radon_average_convolution_integral]:
    nu_epsilon(f)= beta(Phi_epsilon*f) for the original
    measure average in Federer 4.1.18, p. 375. The
    actual scalar convolution graph determines every inner
    integral; no evenness or whole-mass bound is used. *)
Theorem euclidean_kernel_radon_average_convolution_integral (f g:XT->R^o):
  positive_function_lattice (@compactly_supported_continuous_functions R XT) f ->
  is_smoothing_convolution (@scalar_absolute_value_norm R) (family epsilon) f g ->
  is_measure_integral beta (real_total_integrand (fun x:FT=>g (set_val x))) (D f)%:E.
Proof.
move=>hF hConv.
pose mu:=product_measure hAlpha hBeta.
pose hm:=product_measure_is_measure hAlpha hBeta.
pose F:=real_total_integrand (fun z:PT=>w (set_val z.1)*f (set_val z.2+set_val z.1)).
have hWeight:norm_class_zero NX (fun t:R^o=>`|t|) Full w.
  exact:norm_class_continuous
    (@smoothing_reflected_weight_smooth R n phi family hPhi hFamily epsilon hEpsilon 0%N).
have hProduct:=@euclidean_kernel_radon_average_product_integral R n beta hBeta hBetaRadon
  w hWeight
  (@smoothing_reflected_weight_nonnegative R n phi family hPhi hFamily epsilon hEpsilon)
  epsilon (@smoothing_reflected_weight_off R n phi family hPhi hFamily epsilon hEpsilon)
  nu hNu f hF.
have hWhole:=@product_whole_countably_measurable R FT FT alpha beta hAlpha hBeta
  (@current_domain_radon_countably_measurable R n Full hFull alpha hAlpha hAlphaRadon)
  (@current_domain_radon_countably_measurable R n Full hFull beta hBeta hBetaRadon).
have hCount:=@countably_measurable_function_on_countable_source R PT
  (extended_real_line R) mu hm 0 F (@extended_real_zero_closed R) hWhole hProduct.1.
have hOuter:=(@product_function_fubini R FT FT alpha beta hAlpha hBeta F _ hProduct hCount).2.
have hInner(x:FT):is_measure_integral alpha
    (partial_product_horizontal_section F x) (g (set_val x))%:E.
  have hVector:=@smoothing_reflected_translation_integral R n R^o
    (fun t:R^o=>`|t|) (@scalar_absolute_value_norm R) (family epsilon) f g hConv (set_val x).
  have hReal:=@scalar_vector_integral_identification R X
    (@euclidean_lebesgue_measure R n)
    (fun z:X=>w z*f (set_val x+z)) (g (set_val x)) hVector.
  exact:(@euclidean_full_domain_real_integral R n
    (fun z:X=>w z*f (set_val x+z)) (g (set_val x))%:E hReal).
apply:(@measure_integral_graph_equivalent R FT beta _ _ _ _ hOuter)=>x a.
rewrite parameterized_integral_specification real_total_integrand_graph.
split.
- move=>ha;exact:esym (measure_integral_unique ha (hInner x)).
- move=><-;exact:hInner.
Qed.

(** Source for [euclidean_kernel_radon_average_convolution_value]:
    equality of the finite original compact positive
    integrals in the upper variation bound of
    Federer 4.1.18, p. 375. *)
Theorem euclidean_kernel_radon_average_convolution_value (f g:XT->R^o):
  positive_function_lattice (@compactly_supported_continuous_functions R XT) f ->
  positive_function_lattice (@compactly_supported_continuous_functions R XT) g ->
  is_smoothing_convolution (@scalar_absolute_value_norm R) (family epsilon) f g ->
  D f= @radon_positive_compact_integral R FT beta hBeta hBetaRadon
    (fun x:FT=>g (set_val x)).
Proof.
move=>hF hG hConv.
have hFullG:positive_function_lattice (@compactly_supported_continuous_functions R FT)
    (fun x:FT=>g (set_val x)).
  split;first exact:euclidean_full_compact_function_pullback hG.1.
  by move=>x;exact:hG.2 (set_val x).
exact:(EFin_inj (measure_integral_unique
  (euclidean_kernel_radon_average_convolution_integral hF hConv)
  (@radon_positive_compact_integral_laws R FT beta hBeta hBetaRadon _ hFullG))).
Qed.
End EuclideanKernelRadonAverageConvolution.
