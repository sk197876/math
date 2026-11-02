(** Federer (1969), 3.2.7, p. 246, second
    counterexample: a nonmeasurable pullback can become
    measurable after multiplication by a vanishing Jacobian.
    Use the actual projection (x_1,x_2) to (x_1,0),
    the actual characteristic weight, and both area integrals. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology normedtype.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  PlaneAxisProjection NonmeasurableCoordinateCylinder BoundedScalarNonmeasurableSubset
  RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition
  PartialZeroExtension PartialDensityProduct EuclideanJacobianMeasurable Jacobian
  AreaTransformIntegrands AreaIntegralTransformation CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureUP MeasureBasic MeasureSplit MeasureFiniteClosure MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureIntegralUP MeasureConullZeroIntegral LebesgueScalarMeasure HausdorffMeasure LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [projection_weighted_source_zero]: the
    left integrand vanishes in the second example of
    Federer 3.2.7, p. 246. This holds for
    every finite real weight, regardless of measurability,
    because the actual Jacobian is zero everywhere. *)
Lemma projection_weighted_source_zero (R:realType) (g:R_n R 2->R) a:
  partial_function_graph (area_transform_source_integrand (@plane_axis_projection R) setT g) a 0%E.
Proof.
apply/partial_function_zero_extension_graph; left; split; first exact I.
apply/partial_density_product_graph; exists (g (@plane_axis_projection R a))%:E,0%E; split=>//; split; last exact:mule0.
exists 0%R; split=>//.
apply:(euclidean_jacobian_graph 2 setT (@plane_axis_projection R) a 0).2.
exists (@plane_axis_projection R); split; first exact:plane_axis_projection_differential.
exact:plane_axis_projection_jacobian_zero.
Qed.

(** Source for [federer_3_2_7_2]: the complete second
    example of Federer 3.2.7, p. 246.
    The actual unweighted pullback is nonmeasurable,
    but its Jacobian product is everywhere zero and
    both displayed area integrals exist with value zero. *)
Theorem federer_3_2_7_2 (R:realType):
  exists (B:set (real_line_metric R)) (c:R->R),
    is_characteristic_function B c /\ ~measure_measurable (@lebesgue_scalar_measure R) B /\
    ~is_measure_measurable_function (@euclidean_lebesgue_measure R 2)
      (partial_function_total (fun x:inner_metric_space (@euclidean_inner_productP R 2)=>
        (c ((@plane_axis_projection R x) ord0):real_line_metric R))) /\
    is_measure_integral (@euclidean_lebesgue_measure R 2)
      (area_transform_source_integrand (@plane_axis_projection R) setT (fun y=>c (y ord0))) 0%E /\
    is_measure_integral (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2)) 2)
      (area_transform_target_integrand (@plane_axis_projection R) setT (fun y=>c (y ord0))) 0%E.
Proof.
have [B [hBI hNot]]:=@bounded_scalar_nonmeasurable_subset R.
pose c:=@CharacteristicFunction.value R [the choiceType of real_line_metric R] B.
have hc:is_characteristic_function B c:=@CharacteristicFunction.laws R [the choiceType of real_line_metric R] B.
pose X:=inner_metric_space (@euclidean_inner_productP R 2).
pose L:=@plane_axis_projection R.
pose g:=fun y:R_n R 2=>c (y ord0).
have hm:=euclidean_lebesgue_is_measure R 2.
have hSource:is_measure_integral (@euclidean_lebesgue_measure R 2)
    (area_transform_source_integrand L setT g) 0%E.
  apply:(measure_almost_zero_integral hm).
  apply:(@measure_almost_everywhere_mono R [the choiceType of X]
    (@euclidean_lebesgue_measure R 2) hm _ _ _ (measure_almost_everywhere_true hm))=>x _.
  exact:projection_weighted_source_zero.
have hAlt:has_area_transform_alternative L setT g by right; right; exact hSource.1.
have hTarget:=(federer_3_2_5 (leqnn 2) (@plane_axis_projection_lipschitz R)
  (measure_measurable_whole hm) hAlt 0%E).1 hSource.
exists B,c; split; first exact hc; split; first exact hNot; split; last by split.
move=>hMeas; apply:hNot; apply:(euclidean_first_coordinate_cylinder_measurable hc).
have he:partial_function_preimage
    (partial_function_total (fun x:X=>(c ((L x) ord0):real_line_metric R)))
    [set y:real_line_metric R|0<y]=[set x:X|B (x ord0)].
  apply/seteqP; split=>x.
  - move=>[z [hz hPos]].
    change (c ((L x) ord0)=z) in hz.
    change (is_true (0<z)) in hPos.
    rewrite /L plane_axis_projection_head in hz.
    apply:contrapT=>hx.
    by rewrite -hz (characteristic_off_set hc hx) ltxx in hPos.
  - move=>hx; exists 1; split; last exact:ltr01.
    change (c ((L x) ord0)= 1).
    by rewrite /L plane_axis_projection_head (characteristic_on_set hc hx).
rewrite -he; exact (measurable_function_open_preimage hMeas (@open_gt R 0)).
Qed.
