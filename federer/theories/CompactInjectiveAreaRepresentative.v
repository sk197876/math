(** Federer (1969), 3.2.22, pp. 259–260:
    the two compact injective area transformations with
    actual ordinary-Jacobian representatives. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric NormDifferentialUP
  LipschitzUP Rademacher EuclideanLebesgueDimensions EuclideanLebesgueBoxes TopologicalBorel
  EuclideanLinearJacobian Jacobian JacobianUP EuclideanJacobianMeasurable
  PartialFunctionUP PartialFunctionBasic PartialFunctionExtensionUP PartialZeroExtension PartialDensityProduct
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality MeasurableZeroExtension
  MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence MeasureIntegralAlmostEquality
  HausdorffMeasure MappingMultiplicity MappingChartMultiplicity EuclideanCompactMultiplicity
  AreaExtendedTransformIntegrands AreaExtendedFiniteMultiplicity ZeroExtendedDensityWeightAgreement
  TotalScalarCutoff WeightedScalarCutoff RealMetricBackground ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [ordinary_jacobian_representative_extension]:
    supporting actual-value representatives in Federer
    3.2.22, p. 259, from the exact
    Jacobian definition 3.2.1, p. 241.
    Agreement with every actual differential preserves
    precisely every defined scalar Jacobian value. *)
Lemma ordinary_jacobian_representative_extension (R:realType) m n q
    (f:R_n R m->R_n R n) (J:R_n R m->R):
  (forall x D,has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f x D ->J x=euclidean_linear_jacobian q D) ->
  is_partial_function_total_extension (euclidean_jacobian q setT f) J.
Proof.
move=>hJ x j hGraph.
have [D [hD hValue]]:=(euclidean_jacobian_graph q setT f x j).1 hGraph.
exact:(eq_trans (hJ x D hD) hValue).
Qed.

(** Source for [compact_injective_area_representative]:
    the two uses of 3.2.5(2) in Federer
    3.2.22, pp. 259–260. An actual
    ordinary-Jacobian representative changes neither
    integral. Compactness supplies finite multiplicity;
    injectivity turns the target multiplicity into the
    exact image cutoff. The weight may be any
    extended-real function, with no measurability or
    summability hypothesis silently added. *)
Theorem compact_injective_area_representative (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) (A:set (R_n R m))
    (J:R_n R m->R):
  is_metric_lipschitz setT f ->@compact (inner_metric_space (@euclidean_inner_productP R m)) A ->
  (forall x y,A x ->A y ->f x=f y ->x=y) ->
  (forall x D,has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f x D ->J x=euclidean_linear_jacobian m D) ->
  forall (g:R_n R n->\bar R) a,
    is_measure_subset_integral (@euclidean_lebesgue_measure R m) A
      (partial_function_total (fun x=>(g (f x)*(J x)%:E:extended_real_line R))) a <->
    is_measure_subset_integral (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) (f @` A)
      (partial_function_total (fun y=>(g y:extended_real_line R))) a.
Proof.
move=>hF hCompact hInjective hActual g a.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose rho:=@euclidean_lebesgue_measure R m.
have hr:=euclidean_lebesgue_is_measure R m.
have hA:=euclidean_borel_measurable (closed_borel_set (compact_closed (@metric_hausdorff R X) hCompact)).
have hTransform:=area_extended_finite_multiplicity_transform hF hA
  (euclidean_compact_multiplicity_finite hF hCompact) g a.
pose d:=euclidean_jacobian m setT f.
pose p:=total_scalar_cutoff A J.
have hExt:is_partial_function_total_extension d J:=ordinary_jacobian_representative_extension hActual.
have hDomain:measure_almost_everywhere rho (partial_function_domain d).
  apply:(measure_almost_everywhere_mono hr _ (federer_3_1_6 hF))=>x hDiff.
  exact:((euclidean_jacobian_domain m setT f x).2 hDiff).
have hZeroDomain:=zero_extension_conull_domain hr (0%R:real_line_metric R) A hDomain.
have hCutExt:is_partial_function_total_extension
    (partial_function_zero_extension (0%R:real_line_metric R) A d) p.
  move=>x j hj; have [hx|hx]:=pselect (A x).
  - rewrite /p (total_scalar_cutoff_on J hx); exact:(hExt x j ((partial_function_zero_extension_on _ _ _ hx).1 hj)).
  - have hj0:=(partial_function_zero_extension_off _ _ _ hx).1 hj.
    by rewrite /p (total_scalar_cutoff_off J hx) hj0.
have hAgreement:=zero_extended_density_weight_agreement hr
  (fun x=>(g (f x):extended_real_line R)) hZeroDomain hCutExt.
have hSourceGraph:=@weighted_scalar_cutoff_graph R X A (fun x=>g (f x)) J.
have hTargetGraph:=@univalent_multiplicity_weight_graph R X Y A f g hInjective.
split=>hI.
- have hTotal:=measure_integral_graph_equivalent hSourceGraph hI.
  have hOld:=measure_integral_almost_equal hr hTotal (measure_almost_equal_sym hAgreement).
  exact:(measure_integral_graph_equivalent hTargetGraph (hTransform.1 hOld)).
- have hTarget:=measure_integral_graph_equivalent (fun y z=>iff_sym (hTargetGraph y z)) hI.
  have hSource:=measure_integral_almost_equal hr (hTransform.2 hTarget) hAgreement.
  exact:(measure_integral_graph_equivalent (fun x z=>iff_sym (hSourceGraph x z)) hSource).
Qed.
