(** Federer (1969), 4.1.18, p. 375: existence
    of the original average of translated Radon
    measures. The preceding weighted product has
    proper addition on its actual parameter support;
    original 2.6.2 Fubini gives the literal scalar
    translation formula.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormClassOneUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanCartesianMap CurrentDomain CurrentCartesianDomain
  CurrentCartesianDomainMapsSealed CurrentCartesianDomainMapsLaws CurrentCartesianMeasureSealed
  CurrentCartesianMeasureRadon CurrentDomainRadonSigmaFinite EuclideanFullDomainMeasure
  EuclideanCompactParameterAddition EuclideanKernelProductDensity EuclideanTranslatedCompactFunctions
  EuclideanKernelRadonAverageUP MeasureUP MeasureBasic MeasureIntegralUP MeasureIntegralUniqueness
  MeasureIntegralGraphEquivalence MeasureBijectionIntegralTransport PartialFunctionUP PartialFunctionBasic
  PartialFunctionPrecomposition PartialProductSections ParameterizedIntegral ProductMeasure
  ProductFunctionFubini CountablyMeasurableFunctions CountablyMeasurableProduct
  CountablyMeasurableNullModification ExtendedRealOrderTopology SummableRealFunctionUP SummableRealArithmetic
  MeasurePushforward RadonWeightedPushforwardIntegral RadonMeasureUP RadonCompactScalarIntegral
  FunctionLatticeUP CompactSupportFunctionUP EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section EuclideanKernelRadonAverageExistence.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation AB:=(@euclidean_cartesian_set R n n Full Full).
Local Notation FT:=(current_domain R n Full).
Local Notation CT:=(current_domain R (n+n)%N AB).
Local Notation PT:=(Choice.clone (FT*FT)%type _).
Local Notation alpha:=(@euclidean_full_domain_measure R n).
Local Notation hAlpha:=(@euclidean_full_domain_measure_laws R n).1.
Local Notation hAlphaRadon:=(@euclidean_full_domain_measure_laws R n).2.
Variable beta:set FT->\bar R.
Hypotheses (hBeta:is_measure beta) (hBetaRadon:is_radon_measure beta).
Variable w:X->R^o.
Hypothesis hW:norm_class_zero NX (fun t:R^o=>`|t|) Full w.
Hypothesis hPositive:forall z,0<=w z.
Variable r:R.
Hypothesis hOff:forall z,r<NX z->w z= 0.
Local Notation lambda:=(@CartesianCurrentMeasure.value R n n Full Full alpha beta hAlpha hBeta).
Local Notation mu:=(product_measure hAlpha hBeta).
Local Notation hm:=(product_measure_is_measure hAlpha hBeta).
Local Notation J:=(@CartesianCurrentDomain.join R n n Full Full).
Local Notation D:=(@CartesianCurrentDomain.split R n n Full Full).
Local Notation nu:=(@euclidean_kernel_radon_image R n beta hBeta w).
Local Notation hNu:=(@euclidean_kernel_radon_image_laws R n beta hBeta hBetaRadon
  w hW hPositive r hOff).
Local Notation B:=(@radon_positive_compact_integral R FT beta hBeta hBetaRadon).

(** Source for [euclidean_kernel_radon_image_product_integral]:
    the original image integral is exactly the product
    integral of w(z)f(x+z), supporting Federer 4.1.18,
    p. 375, by 2.4.18 and the original block
    coordinate bijection of 2.6.5, p. 120. *)
Theorem euclidean_kernel_radon_image_product_integral (f:XT->R):
  positive_function_lattice (@compactly_supported_continuous_functions R XT) f ->
  is_measure_integral mu
    (real_total_integrand (fun z:PT=>w (set_val z.1)*f (set_val z.2+set_val z.1)))
    (@radon_positive_compact_integral R XT nu hNu.1 hNu.2 f)%:E.
Proof.
move=>hF.
have hOriginal:=@euclidean_kernel_radon_image_compact_integral R n beta hBeta hBetaRadon
  w hW hPositive r hOff f hF.
have hProduct:=(@measure_bijection_integral_iff R PT CT mu lambda hm J D
  (@current_cartesian_measure_bijection R n n Full Full alpha beta hAlpha hBeta) _ _).2 hOriginal.
apply:(@measure_integral_graph_equivalent R PT mu _ _ _ _ hProduct)=>z a.
change (partial_function_graph (real_total_integrand
    (fun y:CT=>f (@euclidean_parameter_addition R n y)*
      w (@euclidean_first_block_map R n n (set_val y)))) (J z) a <->
  partial_function_graph (real_total_integrand
    (fun z:PT=>w (set_val z.1)*f (set_val z.2+set_val z.1))) z a).
rewrite !real_total_integrand_graph.
have hFirst:@euclidean_first_block_map R n n (set_val (J z))= set_val z.1.
  rewrite current_cartesian_domain_join_value.
  exact:(congr1 fst (@euclidean_block_joinK R n n (set_val z.1,set_val z.2))).
have hLast:@euclidean_last_block_map R n n (set_val (J z))= set_val z.2.
  rewrite current_cartesian_domain_join_value.
  exact:(congr1 snd (@euclidean_block_joinK R n n (set_val z.1,set_val z.2))).
by rewrite /euclidean_parameter_addition hFirst hLast mulrC.
Qed.

(** Source for [euclidean_kernel_radon_image_translation_integral]:
    the literal weighted integral of the translated
    original Radon variation is the actual averaged
    measure integral, Federer 4.1.18, p. 375. Every
    inner compact integral exists; no finite whole
    mass or kernel reflection symmetry is required. *)
Theorem euclidean_kernel_radon_image_translation_integral (f:XT->R):
  positive_function_lattice (@compactly_supported_continuous_functions R XT) f ->
  is_measure_integral (@euclidean_lebesgue_measure R n)
    (real_total_integrand (fun z:X=>w z*B (fun x:FT=>f (set_val x+z))))
    (@radon_positive_compact_integral R XT nu hNu.1 hNu.2 f)%:E.
Proof.
move=>hF.
pose F:=real_total_integrand
  (fun z:PT=>w (set_val z.1)*f (set_val z.2+set_val z.1)).
have hProduct:=euclidean_kernel_radon_image_product_integral hF.
have hWhole:=@product_whole_countably_measurable R FT FT alpha beta hAlpha hBeta
  (@current_domain_radon_countably_measurable R n Full hFull alpha hAlpha hAlphaRadon)
  (@current_domain_radon_countably_measurable R n Full hFull beta hBeta hBetaRadon).
have hCount:=@countably_measurable_function_on_countable_source R PT
  (extended_real_line R) mu hm 0 F (@extended_real_zero_closed R) hWhole hProduct.1.
have hOuter:=(@product_function_fubini R FT FT alpha beta hAlpha hBeta F _ hProduct hCount).1.
have hInner(z:FT):is_measure_integral beta
    (partial_product_vertical_section F z)
    (w (set_val z)*B (fun x:FT=>f (set_val x+set_val z)))%:E.
  have hTranslated:=@euclidean_full_translated_positive_compact R n f (set_val z) hF.
  have hBase:=@radon_positive_compact_integral_laws R FT beta hBeta hBetaRadon
    (fun x:FT=>f (set_val x+set_val z)) hTranslated.
  exact:(@real_total_integral_scale R FT beta hBeta _ _ (w (set_val z)) hBase).
have hTotal:is_measure_integral alpha
    (real_total_integrand (fun z:FT=>w (set_val z)*B (fun x:FT=>f (set_val x+set_val z))))
    (@radon_positive_compact_integral R XT nu hNu.1 hNu.2 f)%:E.
  apply:(@measure_integral_graph_equivalent R FT alpha _ _ _ _ hOuter)=>z a.
  rewrite parameterized_integral_specification real_total_integrand_graph.
  split.
  - move=>ha;exact:esym (measure_integral_unique ha (hInner z)).
  - move=><-;exact:hInner.
have hAmbient:=(@real_total_pushforward_integral_iff R FT X alpha hAlpha
  (set_val:FT->X) (fun z:X=>w z*B (fun x:FT=>f (set_val x+z))) hTotal.1 _).1 hTotal.
by rewrite euclidean_full_domain_measure_ambient in hAmbient.
Qed.

(** Source for [euclidean_kernel_radon_average_exists]:
    the original compactly weighted translated Radon
    average exists, supporting Federer 4.1.18, p. 375.
    Its abstract specification retains the original
    scalar translation formula and every outer set. *)
Theorem euclidean_kernel_radon_average_exists:
  exists nu:set XT->\bar R,
    @is_euclidean_kernel_radon_average R n beta hBeta hBetaRadon w nu.
Proof.
exists nu;split;first exact:hNu.1.
split;first exact:hNu.2.
move=>hn hr f hF.
have hI:=euclidean_kernel_radon_image_translation_integral hF.
have hMeasureProof:hn= hNu.1:=Prop_irrelevance _ _.
have hRadonProof:hr= hNu.2:=Prop_irrelevance _ _.
by rewrite hMeasureProof hRadonProof.
Qed.
End EuclideanKernelRadonAverageExistence.
