(** Federer (1969), 3.2.48, pp. 285–286: the
    computed point-dependent tangent exterior norm is the actual
    approximate Jacobian in coarea, almost everywhere on the
    original completed measurable finite rectifiable source pieces. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient GrassmannSubspaces GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormDifferentialUP TangentConeUP EuclideanSubmanifoldUP SubmanifoldTangentPlane
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialExteriorNormUP
  MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic MeasureApproximateJacobianUP
  MeasureApproximateJacobian HausdorffMeasure RectifiableSetUP SubmanifoldSubsetApproximateTangent
  AmbientApproximateDifferentialRestriction TangentIsometryPartialJacobian.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [submanifold_subset_variable_jacobian_almost]: supporting
    the computed variable Jacobian in 3.2.48, p. 286,
    by the original tangent agreement of 3.2.19,
    p. 256. Only actual pointwise differentials and
    tangent exterior norms are obligations. No measurable
    derivative field, constant Jacobian, rank or additional
    Jacobian-measurability premise is assumed. *)
Theorem submanifold_subset_variable_jacobian_almost (R:realType) n p mu k q
    (S K:set (R_n R n)) (F:R_n R n->R_n R p) (j:R_n R n->R):
  (1<=k)%N ->@is_euclidean_submanifold R n mu k S ->K `<=` S ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (InnerMetric.inner_metric_space (@euclidean_inner_productP R n)) mu) mu K ->
  measure_measurable (@hausdorff_measure R
    (InnerMetric.inner_metric_space (@euclidean_inner_productP R n)) mu) K ->
  (forall a,K a ->exists D:Hom (R_n R n) (R_n R p),
    has_norm_differential (inner_norm (@euclidean_inner_productP R n))
      (inner_norm (@euclidean_inner_productP R p)) (fun _=>True) F a D /\
    is_partial_exterior_norm q
      (partial_function_source_restrict
        (norm_tangent_cone (inner_norm (@euclidean_inner_productP R n)) S a)
        (partial_function_total D)) (j a)) ->
  let H:=@hausdorff_measure R (InnerMetric.inner_metric_space (@euclidean_inner_productP R n)) mu in
  measure_almost_everywhere_on H K [set a|partial_function_graph
    (measure_approximate_jacobian (measure_restrict H K) mu q
      (partial_function_source_restrict K (partial_function_total F))) a (j a)].
Proof.
move=>hk hS hKS hRect hMeas hValues H.
have hH:=@hausdorff_measure_is_measure R
  (InnerMetric.inner_metric_space (@euclidean_inner_productP R n)) mu.
have hTan:=@submanifold_subset_approximate_tangent_almost R n mu k S K hk hS hKS hRect hMeas.
apply:(measure_null_subset hH _ hTan)=>a [ha hn]; split; first exact ha.
move=>hT; apply:hn.
have [D [hD hN]]:=hValues a ha.
apply:(measure_approximate_jacobian_graph _ _ _ _ _ _).2.
exists (partial_function_source_restrict
  (MeasureApproximateTangentUP.measure_approximate_tangent_cone
    (inner_norm_real_norm (@euclidean_inner_productP R n)) (measure_restrict H K) mu a)
  (partial_function_total D)); split.
- exact:(@ambient_differential_restricted_approximate_graph R (R_n R n) (R_n R p)
    (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R p))
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R p)) H mu K F a D hH hD).
- by rewrite hT.
Qed.
