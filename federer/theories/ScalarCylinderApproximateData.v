(** Federer (1969), 3.2.33, p. 270: actual ordinary
    and approximate differentials and Jacobians of the smooth map. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  NormDifferentialUP NormHigherCurveDerivativeUP RealOpenIntervals PartialFunctionUP PartialFunctionBasic
  PartialFunctionSourceRestriction MeasureUP MeasureRestriction HausdorffMeasure
  MeasureApproximateDifferentialUP MeasureApproximateJacobianUP PartialExteriorTotalLinear EuclideanLinearJacobian
  OpenEuclideanApproximateTangent NormDifferentialRestrictedApproximate EuclideanOpenUnitCube
  ScalarCylinderMapUP ScalarCylinderDifferential ScalarCylinderJacobianLower IntervalBumpPrimitiveUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_cylinder_actual_approximate_data]:
    interpret the displayed Df and J_mu f of Federer
    3.2.33, p. 270, using the precise original-domain
    approximate objects of 3.2.32. At EVERY cube point the
    approximate tangent is the entire source and the actual
    ordinary linear differential has exactly the approximate
    graph. Every exterior-degree Jacobian agrees, and the
    printed mu-Jacobian is at least one, including mu=0. *)
Theorem scalar_cylinder_actual_approximate_data (R:realType) mu k (a b:nat->R) (psi g:R->R)
    (F:R_n R ((mu+1)+k)->R_n R (mu+1)):
  is_scalar_cylinder_map g F ->is_interval_bump_primitive a b psi g ->
  forall x,euclidean_open_unit_cube x ->
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R ((mu+1)+k))) ((mu+1)+k) in
  let W:=@euclidean_open_unit_cube R ((mu+1)+k) in
  let f:=partial_function_source_restrict W (partial_function_total F) in
  exists L:Hom (R_n R ((mu+1)+k)) (R_n R (mu+1)),
    is_scalar_cylinder_map (fun t=>psi (x (lshift k (rshift mu ord0)))*t) L /\
    has_norm_differential (inner_norm (@euclidean_inner_productP R ((mu+1)+k)))
      (inner_norm (@euclidean_inner_productP R (mu+1))) W F x L /\
    is_measure_approximate_differential (inner_norm (@euclidean_inner_productP R (mu+1)))
      (inner_norm_real_norm (@euclidean_inner_productP R ((mu+1)+k)))
      (measure_restrict H W) ((mu+1)+k) f x (partial_function_total L) /\
    (forall q,has_measure_approximate_jacobian (measure_restrict H W) ((mu+1)+k) q f x
      (euclidean_linear_jacobian q L)) /\1<=euclidean_linear_jacobian mu L.
Proof.
move=>hF hPrimitive x hx H W f.
have hxT:real_open_interval 0 1 (x (lshift k (rshift mu ord0))).
  have /andP [h0 h1]:=hx (lshift k (rshift mu ord0)); by split.
have [L [hL hD]]:=scalar_cylinder_actual_differential hF hx (interval_primitive_differential hPrimitive hxT).
have hH:=@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R ((mu+1)+k))) ((mu+1)+k).
have hApprox:=@norm_differential_restricted_measure_approximate R
  (R_n R ((mu+1)+k)) (R_n R (mu+1))
  (inner_norm (@euclidean_inner_productP R ((mu+1)+k))) (inner_norm (@euclidean_inner_productP R (mu+1)))
  (inner_norm_real_norm (@euclidean_inner_productP R ((mu+1)+k))) H W ((mu+1)+k) F x L hH hD.
have hFull:=open_euclidean_approximate_tangent_full (norm_differential_interior hD).
have hTotal:=@full_cone_approximate_differential_total_graph R
  (R_n R ((mu+1)+k)) (R_n R (mu+1))
  (inner_norm (@euclidean_inner_productP R ((mu+1)+k))) (inner_norm (@euclidean_inner_productP R (mu+1)))
  (inner_norm_real_norm (@euclidean_inner_productP R ((mu+1)+k)))
  (inner_norm_real_norm (@euclidean_inner_productP R (mu+1)))
  (measure_restrict H W) ((mu+1)+k) f x L (measure_restrict_is_measure hH W) hApprox hFull.
exists L; split; first exact hL.
split; first exact hD.
split; first exact hTotal.
split; last exact:(scalar_cylinder_jacobian_lower_bound hL).
move=>q; exists (partial_function_total L); split; first exact hTotal.
exact:(partial_exterior_total_linear_norm q L).
Qed.
