(** Federer (1969), 3.2.48, pp. 285–286: the actual tangent
    Jacobian profile is the actual approximate Jacobian almost everywhere
    on the original completed measurable source subset. The profile
    uses the existing sealed partial exterior norm, without a selected
    orientation, tangent frame or extra measurable-field hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  NormDifferentialUP TangentConeUP EuclideanSubmanifoldUP EuclideanTangentExteriorNorm
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  MeasureUP MeasureRestriction MeasureAlmostUP MeasureApproximateJacobian
  HausdorffMeasure RectifiableSetUP SubmanifoldSubsetVariableJacobian.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [submanifold_subset_intrinsic_jacobian_almost]: the
    reduction to manifold tangents in 3.2.48, p. 285, with the original
    approximate Jacobian restored for coarea. Every actual ambient
    differential is proved; its field need not be supplied as measurable. *)
Theorem submanifold_subset_intrinsic_jacobian_almost (R:realType) n p mu q
    (M W:set (R_n R n)) (F:R_n R n->R_n R p)
    (D:R_n R n->Hom (R_n R n) (R_n R p)):
  @is_euclidean_submanifold R n mu 1%N M ->W `<=` M ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) mu) mu W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) mu) W ->
  (forall a,W a ->has_norm_differential (inner_norm (@euclidean_inner_productP R n))
    (inner_norm (@euclidean_inner_productP R p)) (fun _=>True) F a (D a)) ->
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) mu in
  measure_almost_everywhere_on H W [set a|partial_function_graph
    (measure_approximate_jacobian (measure_restrict H W) mu q
      (partial_function_source_restrict W (partial_function_total F))) a
    (@euclidean_tangent_exterior_norm R n p q M a (D a))].
Proof.
move=>hM hWM hRW hMW hD H.
apply:(@submanifold_subset_variable_jacobian_almost R n p mu 1%N q M W F
  (fun a=>@euclidean_tangent_exterior_norm R n p q M a (D a))
  (leqnn 1) hM hWM hRW hMW).
move=>a ha; exists (D a); split; first exact (hD a ha).
exact (@euclidean_tangent_exterior_normP R n p q M a (D a)).
Qed.
