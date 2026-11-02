(** Federer (1969), 3.2.33, p. 270: the original
    public approximate mu-Jacobian equals one everywhere on X. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionPostcomposition
  MeasureRestriction HausdorffMeasure ExtendedRealOrderTopology MeasureApproximateJacobian
  RectifiablePositiveFibreCoareaUP EuclideanOpenUnitCube RealOpenIntervals
  ScalarCylinderMapUP ScalarCylinderApproximateData ScalarCylinderZeroJacobian ScalarCylinderCriticalSet IntervalBumpPrimitiveUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_cylinder_critical_jacobian_one]: the
    actual integrand in the last display of Federer 3.2.33,
    p. 270. The printed sufficient lower bound is here
    strengthened to equality on X, where the scalar derivative
    vanishes. Every value belongs to the original public partial
    Jacobian graph; no total-field completion or substituted
    differential is used in the displayed integral. *)
Theorem scalar_cylinder_critical_jacobian_one (R:realType) mu k (a b:nat->R) (psi g:R->R)
    (F:R_n R ((mu+1)+k)->R_n R (mu+1)):
  is_scalar_cylinder_map g F ->is_interval_bump_primitive a b psi g ->
  let f:=partial_function_source_restrict (@euclidean_open_unit_cube R ((mu+1)+k)) (partial_function_total F) in
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R ((mu+1)+k))) ((mu+1)+k) in
  forall x,partial_approximate_image_dimension_locus ((mu+1)+k) mu f x ->
    partial_function_graph (extended_measure_approximate_jacobian (measure_restrict H (partial_function_domain f))
      ((mu+1)+k) mu f) x (1%E:extended_real_line R).
Proof.
move=>hF hPrimitive f H x hx.
have hDom:partial_function_domain f=@euclidean_open_unit_cube R ((mu+1)+k).
  by rewrite /f partial_function_source_restrict_domain partial_function_total_domain setIT.
have hCritical:=scalar_cylinder_exact_critical_source hF hPrimitive.
change ((partial_approximate_image_dimension_locus ((mu+1)+k) mu f) x) in hx.
rewrite /f hCritical in hx.
have [hWx [hxT hNot]]:=hx.
have hZero:psi (x (lshift k (rshift mu ord0)))= 0:=
  (interval_primitive_zero_coefficient hPrimitive hxT).2 hNot.
have [L [hL [hD [hTotal [hJ hLower]]]]]:=scalar_cylinder_actual_approximate_data hF hPrimitive hWx.
have hZeroL:is_scalar_cylinder_map (fun _=>0) L.
  constructor; first exact:(scalar_cylinder_first_coordinates hL).
  move=>v; have h:=scalar_cylinder_last_coordinate hL v.
  by rewrite hZero mul0r in h.
have hOne:=hJ mu.
rewrite (scalar_cylinder_zero_jacobian hZeroL) in hOne.
rewrite hDom /extended_measure_approximate_jacobian.
exists (1:R); split; last reflexivity.
exact:(@measure_approximate_jacobian_graph R ((mu+1)+k) (mu+1)
  (measure_restrict H (@euclidean_open_unit_cube R ((mu+1)+k))) ((mu+1)+k) mu f x 1).2 hOne.
Qed.
