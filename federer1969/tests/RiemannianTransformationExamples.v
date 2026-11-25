(** Federer (1969), 3.2.46, pp. 281–282: concrete checks of
    the actual volume, signed area and signed coarea formulas. The
    positive zero-dimensional atom and the line with length scale
    two test normalization, singular maps and signed integrals. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RiemannianTensorUP RiemannianConstantTensor RiemannianScaledLine
  RiemannianMetricCarrier RiemannianHausdorff RiemannianChartVolumeDensity
  RiemannianVolumeDerivate MetricSubsetBackground ContinuousPositiveDensityDerivate MeasureDerivates
  RiemannianVolumeIntegral RiemannianVolumeDensity RiemannianChartVolumeIntegral
  RiemannianDisconnectedChart RiemannianConstantMap RiemannianConstantJacobian RiemannianMapJacobian
  RiemannianAreaTransformIntegrands RiemannianAreaIntegralTransformation
  RiemannianWeightedCoarea RiemannianCoareaFibreIntegral
  ExtendedRealOrderTopology RealMetricBackground PartialFunctionUP PartialFunctionBasic PartialDensityProduct
  PartialZeroExtension PartialZeroExtensionLaws PartialFunctionPostcomposition
  PartialExtendedArithmetic MappingMultiplicity CountingMeasure CountingInjectionBound
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes LebesgueScalarMeasure
  MeasureUP MeasureBasic MeasureSplit MeasureAlmostBasic MeasurableTotalBasic MeasureSubsetIntegral
  MeasureSubsetConstantIntegral MeasureIntegralUP MeasureIntegralGraphEquivalence
  MeasureIntegralUniqueness MeasureIntegralNegationLaw MeasureDensityUP MeasureIntegralBounds
  RiemannianVolumeIdentification RiemannianChartReference RiemannianReferencePushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [negative_unit_integral_regression_support]: the
    signed-constant calculation of 2.4.4(3), p. 82, used to
    test the genuinely signed formulas of 3.2.46, p. 282.
    The measured space may have infinite mass. *)
Lemma negative_unit_integral_regression_support (R:realType) (X:choiceType)
    (mu:set X->extended_real_line R):
  is_measure mu -> is_measure_integral mu
    (partial_function_total (fun _:X=>(-1:R)%:E)) (-mu setT)%E.
Proof.
move=>hMu.
have hOne:=measure_nonnegative_constant_subset_integral hMu
  (measure_measurable_whole hMu) (ler01 : (0<= 1 :> extended_real_line R)%E).
rewrite mul1e in hOne.
have hTotal:=measure_integral_graph_equivalent
  (partial_zero_extension_whole_graph (0:extended_real_line R)
    (partial_function_total (fun _:X=>(1:R)%:E))) hOne.
have hNegative:=measure_integral_negation hMu hTotal.
apply:(measure_integral_graph_equivalent _ hNegative)=>x z.
split.
- move=>[v [hv hz]]; change ((1:R)%:E=v) in hv.
  change ((-1:R)%:E=z); by rewrite -hz -hv EFinN.
- move=>hz; exists (1:R)%:E; split; first by [].
  change ((-1:R)%:E=z) in hz; by rewrite -hz EFinN.
Qed.

Section ZeroAtom.
Variable R:realType.
Local Notation hz := (riemannian_constant_tensor (@euclidean_inner_productP R 0)).
Local Notation Z := (riemannian_metric_space hz).
Local Notation beta := (riemannian_hausdorff_measure hz 0 (ler0n R 0)).

(** Source for [riemannian_zero_chart_unique_regression_support]:
    R^0 has one actual point, retaining the positive atom in
    3.2.46, pp. 281–282; see 2.10.2, p. 171. *)
Lemma riemannian_zero_chart_unique_regression_support (x y:Z):x=y.
Proof. apply:val_inj; apply/ffunP=>i; by move:(ltn_ord i); rewrite ltn0. Qed.

(** Source for [riemannian_positive_zero_atom_example]: the actual
    Riemannian H^0 volume of the whole zero-dimensional chart is
    one, testing 3.2.46, pp. 281–282, without a zero-mass convention. *)
Example riemannian_positive_zero_atom_example:beta setT=(1:R)%:E.
Proof.
pose b:Z:=@exist (R_n R 0) (fun z=>z \in @setT (R_n R 0)) 0 (mem_set I).
have hSet:setT=[set b].
  apply/seteqP; split=>x _; first exact:riemannian_zero_chart_unique_regression_support.
  by [].
rewrite hSet riemannian_hausdorff_zero_counting.
exact:counting_measure_singleton_value.
Qed.

(** Source for [riemannian_signed_zero_area_example]: actual signed
    area, 3.2.46, p. 282, extending 3.2.5, p. 244, on
    the zero-dimensional chart. The constant map has actual zeroth
    Jacobian one, one source point and multiplicity one. Both genuine
    integrals equal minus one. *)
Example riemannian_signed_zero_area_example:
  exists f:Z->Z, exists u:Z->R,
    is_measure_integral beta (riemannian_area_source_integrand f setT u) (-1:R)%:E /\
    is_measure_integral beta (riemannian_area_target_integrand f setT u) (-1:R)%:E.
Proof.
pose b:Z:=@exist (R_n R 0) (fun z=>z \in @setT (R_n R 0)) 0 (mem_set I).
pose f:=fun _:Z=>b.
pose u:=fun _:Z=>(-1:R).
have hMu:=riemannian_hausdorff_is_measure hz (ler0n R 0).
have hMultiplicity y:@mapping_multiplicity R _ _ f setT y=(1:R)%:E.
  have hSet:mapping_fibre f setT y=[set b].
    apply/seteqP; split=>x hx.
    + exact:riemannian_zero_chart_unique_regression_support.
    + split; first by [].
      exact:riemannian_zero_chart_unique_regression_support.
  by rewrite /mapping_multiplicity hSet counting_measure_singleton_value.
have hNegative:=negative_unit_integral_regression_support hMu.
rewrite riemannian_positive_zero_atom_example -EFinN in hNegative.
have hTarget:is_measure_integral beta (riemannian_area_target_integrand f setT u) (-1:R)%:E.
  apply:(measure_integral_graph_equivalent _ hNegative)=>x z.
  by rewrite /riemannian_area_target_integrand /f /u /partial_function_total /= hMultiplicity mule1.
have hAlt:has_riemannian_area_transform_alternative f (ler0n R 0) setT u.
  left; exact (@measurable_total_constant R [the choiceType of Z]
    [the topologicalType of real_line_metric R] beta hMu (-1:R)).
have hArea:=@federer_3_2_46_area R 0 0 _ _ _ _ hz hz f (ler0n R 0)
  setT u (leqnn 0) (riemannian_constant_map_lipschitz hz b)
  (measure_measurable_whole hMu) hAlt (-1:R)%:E.
exists f,u; split; [exact:hArea.2 hTarget |exact hTarget].
Qed.
End ZeroAtom.

Section ScaledLine.
Variable R:realType.
Local Notation hg := (riemannian_scaled_line_tensor R).
Local Notation M := (riemannian_metric_space hg).
Local Notation mu := (riemannian_hausdorff_measure hg 1 (ler0n R 1)).
Local Notation phi := (@riemannian_chart_reference R 1 setT
  (fun _=>@riemannian_scaled_line_form R) hg).

(** Source for [riemannian_scaled_unit_interval_volume_example]:
    volume formula of 3.2.46, p. 282, for the actual unit
    coordinate interval and the genuine tensor of length scale two.
    Its original-rho H^1 measure equals two, retaining the
    square-root discriminant rather than the ordinary unit length. *)
Example riemannian_scaled_unit_interval_volume_example:
  mu [set x:M|forall i:'I_1, 0<val x i<1]=(2:R)%:E.
Proof.
pose E:=inner_metric_space (@euclidean_inner_productP R 1).
pose C:set E:=[set x|forall i:'I_1,0<x i<1].
pose S:set M:=(fun x:M=>(val x:E)) @^-1` C.
have hC:measure_measurable (@euclidean_lebesgue_measure R 1) C.
  have hBox:C=euclidean_coordinate_box (fun _:'I_1=>`]0,1[).
    apply/seteqP; split=>x hx i; have:=hx i; by rewrite /= in_itv.
  rewrite hBox; exact (@euclidean_coordinate_box_measure R 1
    (fun _:'I_1=>`]0,1[)
    (fun _=>@lebesgue_scalar_open_interval_measurable R 0 1)).1.
have hS:=@riemannian_reference_measurable_preimage R 1 setT
  (fun _=>@riemannian_scaled_line_form R) hg C hC.
have hImage:(fun x:M=>(val x:E)) @` S=C.
  apply/seteqP; split=>x; first by move=>[y hy <-].
  move=>hx; exists (@exist E (fun z=>z \in @setT E) x (mem_set I)); first exact hx; by [].
have hPhi:phi S=(1:R)%:E.
  by rewrite riemannian_chart_reference_value hImage /C euclidean_unit_cube.
have hTwo:(0<=(2:R)%:E)%E by rewrite lee_fin ler0n.
have hConstant:=measure_nonnegative_constant_subset_integral
  (@riemannian_chart_reference_is_measure R 1 setT
    (fun _=>@riemannian_scaled_line_form R) hg) hS
    hTwo.
rewrite hPhi -EFinM mulr1 in hConstant.
have hVolume:=@riemannian_chart_volume_integral R 1 setT
  (fun _=>@riemannian_scaled_line_form R) hg (ler0n R 1) S hS.
have hSame:is_measure_subset_integral phi S
    (partial_function_total (fun x:M=>(riemannian_chart_volume_density hg x)%:E)) (2:R)%:E.
  apply:(measure_integral_graph_equivalent _ hConstant)=>x z.
  rewrite !partial_function_zero_extension_graph /partial_function_total /=
    riemannian_scaled_line_density; by [].
exact (measure_integral_unique hVolume hSame).
Qed.

(** Source for [riemannian_scaled_line_derivate_example]: the
    actual pointwise volume derivate in 3.2.46, p. 281,
    is two at every point of the length-scale-two line. This
    tests the exact derivate graph, rather than an almost-everywhere
    substitute or a supplied derivative value. *)
Example riemannian_scaled_line_derivate_example
    (a:@metric_subset R [the metricType R of
      inner_metric_space (@euclidean_inner_productP R 1)] setT):
  partial_function_graph
    (@measure_derivate R
      [the metricType R of @metric_subset R
        [the metricType R of inner_metric_space (@euclidean_inner_productP R 1)] setT]
      mu phi (positive_finite_containing_relation phi)) a (2:R)%:E.
Proof.
have hDerivate:=@federer_3_2_46_volume_derivate R 1 setT
  (fun _=>@riemannian_scaled_line_form R) hg (ler0n R 1) a.
by rewrite riemannian_scaled_line_density in hDerivate.
Qed.

(** Source for [riemannian_scaled_signed_coarea_example]: the
    full signed coarea assertion of 3.2.46, p. 282, for the
    actual constant map from the length-scale-two line to R^0.
    Its original Jacobian is one everywhere; both genuine integrals
    equal minus the actual whole-line volume. The proved unit
    interval volume makes this a nonzero signed test. No finiteness
    of the whole volume or independent inner integrability is assumed. *)
Example riemannian_scaled_signed_coarea_example:
  let hz:=riemannian_constant_tensor (@euclidean_inner_productP R 0) in
  exists f:M->riemannian_metric_space hz,
    (0<mu setT)%E /\
    is_measure_integral mu
      (partial_density_product (partial_function_total (fun _:M=>(-1:R)%:E))
        (extended_riemannian_map_jacobian f 0)) (-mu setT)%E /\
    is_measure_integral (riemannian_hausdorff_measure hz 0 (ler0n R 0))
      (riemannian_coarea_fibre_integral f (ler0n R 1)
        (partial_function_total (fun _:M=>(-1:R)%:E))) (-mu setT)%E.
Proof.
move=>hz.
pose b:riemannian_metric_space hz:=@exist (R_n R 0) (fun z=>z \in @setT (R_n R 0)) 0 (mem_set I).
pose f:=fun _:M=>b.
have hMu:=riemannian_hausdorff_is_measure hg (ler0n R 1).
have hNegative:=negative_unit_integral_regression_support hMu.
have [a [hLeft hRight]]:=@riemannian_weighted_coarea_formula R 1 0
  setT setT (fun _=>@riemannian_scaled_line_form R)
  (fun _=>@euclidean_inner_product R 0) hg hz f (ler0n R 1) (ler0n R 0) (ler0n R 1)
  (partial_function_total (fun _:M=>(-1:R)%:E)) (ltn0Sn 0)
  (riemannian_constant_map_lipschitz hg b) (ex_intro _ _ hNegative).
have hProduct x z:partial_function_graph
    (partial_density_product (partial_function_total (fun _:M=>(-1:R)%:E))
      (extended_riemannian_map_jacobian f 0)) x z <->
    partial_function_graph (partial_function_total (fun _:M=>(-1:R)%:E)) x z.
  rewrite partial_density_product_graph; split.
  - move=>[u [v [hu [hv he]]]].
    have hV: v=(1:R)%:E:=(riemannian_constant_zeroth_jacobian b x v).1 hv.
    by rewrite hV mule1 in he; rewrite -he.
  - move=>hu; exists (-1:R)%:E,(1:R)%:E; split; first by [].
    split; last by rewrite mule1.
    exact:(riemannian_constant_zeroth_jacobian b x (1:R)%:E).2 erefl.
have hOriginal:=measure_integral_graph_equivalent hProduct hLeft.
have hValue:a=(-mu setT)%E:=measure_integral_unique hOriginal hNegative.
rewrite hValue in hLeft hRight.
exists f; split; last by split.
apply:lt_le_trans _ (@measure_mono R [the choiceType of M] mu hMu
  [set x:M|forall i:'I_1,0<val x i<1] setT (subsetT _)).
rewrite riemannian_scaled_unit_interval_volume_example lte_fin; exact:ltr0n.
Qed.
End ScaledLine.
