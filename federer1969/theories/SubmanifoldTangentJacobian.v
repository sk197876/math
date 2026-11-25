(** Federer (1969), 3.2.28, pp. 265–267:
    the calculated tangent exterior norms are the actual
    intrinsic approximate Jacobians used by area and coarea,
    almost everywhere on the measurable finite-mass manifold. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient GrassmannSubspaces GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormDifferentialUP TangentConeUP EuclideanSubmanifoldUP SubmanifoldTangentPlane
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialExteriorNormUP
  MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic MeasureApproximateJacobianUP
  MeasureApproximateJacobian HausdorffMeasure RectifiableSetUP SubmanifoldApproximateTangent
  AmbientApproximateDifferentialRestriction TangentIsometryPartialJacobian.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [submanifold_tangent_jacobian_almost]: the
    passage from the computed tangent Jacobian to the
    actual approximate Jacobian in Federer 3.2.28,
    pp. 265–267, by 3.2.16 and 3.2.19,
    pp. 253,256. No assertion at exceptional points
    or totalized value outside the tangent is made. *)
Theorem submanifold_tangent_jacobian_almost (R:realType) n p mu k q
    (S:set (R_n R n)) (F:R_n R n->R_n R p) j:
  (1<=k)%N ->@is_euclidean_submanifold R n mu k S ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (InnerMetric.inner_metric_space (@euclidean_inner_productP R n)) mu) mu S ->
  measure_measurable (@hausdorff_measure R
    (InnerMetric.inner_metric_space (@euclidean_inner_productP R n)) mu) S ->
  (forall a,S a ->exists D:Hom (R_n R n) (R_n R p),
    has_norm_differential (inner_norm (@euclidean_inner_productP R n))
      (inner_norm (@euclidean_inner_productP R p)) (fun _=>True) F a D /\
    is_partial_exterior_norm q
      (partial_function_source_restrict
        (norm_tangent_cone (inner_norm (@euclidean_inner_productP R n)) S a)
        (partial_function_total D)) j) ->
  let H:=@hausdorff_measure R (InnerMetric.inner_metric_space (@euclidean_inner_productP R n)) mu in
  measure_almost_everywhere_on H S [set a|partial_function_graph
    (measure_approximate_jacobian (measure_restrict H S) mu q
      (partial_function_source_restrict S (partial_function_total F))) a j].
Proof.
move=>hk hS hRect hMeas hValues H.
have hH:=@hausdorff_measure_is_measure R
  (InnerMetric.inner_metric_space (@euclidean_inner_productP R n)) mu.
have hTan:=@submanifold_approximate_tangent_almost R n mu k S hk hS hRect hMeas.
apply:(measure_null_subset hH _ hTan)=>a [ha hn]; split; first exact ha.
move=>hT; apply:hn.
have [D [hD hN]]:=hValues a ha.
apply:(measure_approximate_jacobian_graph _ _ _ _ _ _).2.
exists (partial_function_source_restrict
  (MeasureApproximateTangentUP.measure_approximate_tangent_cone
    (inner_norm_real_norm (@euclidean_inner_productP R n)) (measure_restrict H S) mu a)
  (partial_function_total D)); split.
- exact:(@ambient_differential_restricted_approximate_graph R (R_n R n) (R_n R p)
    (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R p))
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R p)) H mu S F a D hH hD).
- by rewrite hT.
Qed.

(** Source for [submanifold_tangent_isometry_jacobian_one]:
    an actual tangent-isometric differential has approximate
    Jacobian one almost everywhere, as used in Federer
    3.2.28(4), pp. 266–267. The actual tangent
    plane and its dimension are supplied by 3.1.21. *)
Theorem submanifold_tangent_isometry_jacobian_one (R:realType) n p mu k
    (S:set (R_n R n)) (F:R_n R n->R_n R p):
  (1<=k)%N ->@is_euclidean_submanifold R n mu k S ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (InnerMetric.inner_metric_space (@euclidean_inner_productP R n)) mu) mu S ->
  measure_measurable (@hausdorff_measure R
    (InnerMetric.inner_metric_space (@euclidean_inner_productP R n)) mu) S ->
  (forall a,S a ->exists D:Hom (R_n R n) (R_n R p),
    has_norm_differential (inner_norm (@euclidean_inner_productP R n))
      (inner_norm (@euclidean_inner_productP R p)) (fun _=>True) F a D /\
    forall x y,norm_tangent_cone (inner_norm (@euclidean_inner_productP R n)) S a x ->
      norm_tangent_cone (inner_norm (@euclidean_inner_productP R n)) S a y ->
      euclidean_inner_product (D x) (D y)=euclidean_inner_product x y) ->
  let H:=@hausdorff_measure R (InnerMetric.inner_metric_space (@euclidean_inner_productP R n)) mu in
  measure_almost_everywhere_on H S [set a|partial_function_graph
    (measure_approximate_jacobian (measure_restrict H S) mu mu
      (partial_function_source_restrict S (partial_function_total F))) a 1].
Proof.
move=>hk hS hRect hMeas hD.
apply:(@submanifold_tangent_jacobian_almost R n p mu k mu S F 1 hk hS hRect hMeas).
move=>a ha; have [D [hDiff hPair]]:=hD a ha; exists D; split; first exact hDiff.
have [T hT]:=@submanifold_tangent_plane R n mu k S a hk hS ha.
apply:(@tangent_isometry_partial_jacobian_one R n p mu T D).
- move=>x y hx hy; apply:hPair; by rewrite hT.
- move=>v w; change ((norm_tangent_cone (inner_norm (@euclidean_inner_productP R n)) S a v /\D v=w)<->
    grassmann_val T v /\D v=w).
  by rewrite hT.
Qed.
