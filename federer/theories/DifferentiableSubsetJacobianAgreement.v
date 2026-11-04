(** Federer (1969), 3.2.48, p. 285: replacing the
    original measurable source by countably many manifold pieces does
    not change its approximate Jacobian almost everywhere on each
    piece. Actual ambient differentiability replaces global Lipschitzness. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  NormDifferentialUP PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic HausdorffMeasure
  MeasureApproximateTangentUP MeasureApproximateDifferentialUP MeasureApproximateDifferentialUniqueness
  AmbientApproximateDifferentialRestriction MeasureApproximateJacobianUP MeasureApproximateJacobian
  FiniteMeasurableTangentRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [differentiable_subset_jacobian_agreement]: the source
    restriction implicit in 3.2.48, p. 285, by 3.2.16 and
    2.10.19(4). Equality of actual completed-source tangent cones
    and the actual ambient differential identifies both Jacobian
    graphs in every degree. No derivative field is selected. *)
Theorem differentiable_subset_jacobian_agreement (R:realType) m n v q
    (W S:set (R_n R n)) (F:R_n R n->R_n R v):
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m in
  measure_measurable H W ->measure_measurable H S ->S `<=` W ->(H W< +oo)%E ->
  (forall x,S x ->exists D:Hom (R_n R n) (R_n R v),
    has_norm_differential (inner_norm (@euclidean_inner_productP R n))
      (inner_norm (@euclidean_inner_productP R v)) (fun _=>True) F x D) ->
  measure_almost_everywhere_on H S [set x|forall j,
    partial_function_graph (measure_approximate_jacobian (measure_restrict H W) m q
      (partial_function_source_restrict W (partial_function_total F))) x j <->
    partial_function_graph (measure_approximate_jacobian (measure_restrict H S) m q
      (partial_function_source_restrict S (partial_function_total F))) x j].
Proof.
move=>H hW hS hSW hFinite hDiff.
have hH:=@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.
have hCones:=@finite_measurable_subset_approximate_tangent_equal R m n W S hW hS hSW hFinite.
apply:(measure_null_subset hH _ hCones)=>x [hx hNot]; split; first exact hx.
move=>hCone; apply hNot.
have [D hD]:=hDiff x hx.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose NY:=inner_norm (@euclidean_inner_productP R v).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R v).
pose d0:=partial_function_source_restrict
  (measure_approximate_tangent_cone hNX (measure_restrict H W) m x) (partial_function_total D).
have hDW:=@ambient_differential_restricted_approximate_graph R (R_n R n) (R_n R v)
  NX NY hNX hNY H m W F x D hH hD.
have hDS:=@ambient_differential_restricted_approximate_graph R (R_n R n) (R_n R v)
  NX NY hNX hNY H m S F x D hH hD.
rewrite hCone in hDS.
have hGraphs d:is_measure_approximate_differential NY hNX (measure_restrict H W) m
    (partial_function_source_restrict W (partial_function_total F)) x d <->
    is_measure_approximate_differential NY hNX (measure_restrict H S) m
    (partial_function_source_restrict S (partial_function_total F)) x d.
  split=>hd.
  - have hSame:=measure_approximate_differential_unique hd hDW.
    by rewrite hSame.
  - have hSame:=measure_approximate_differential_unique hd hDS.
    by rewrite hSame.
move=>j; rewrite !measure_approximate_jacobian_graph.
split.
- move=>[d [hd hNorm]]; exists d; split; last exact hNorm.
  exact ((hGraphs d).1 hd).
- move=>[d [hd hNorm]]; exists d; split; last exact hNorm.
  exact ((hGraphs d).2 hd).
Qed.
