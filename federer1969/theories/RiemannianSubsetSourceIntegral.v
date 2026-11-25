(** Federer (1969), 3.2.46, p. 282: restore
    actual Riemannian source volume on the original
    measurable subset. Exact zero-extension graph laws
    preserve signed definedness and the original Jacobian
    domain through the source-density cancellation. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations RiemannianTensorUP
  RiemannianMetricCarrier RiemannianHausdorff RiemannianChartReference
  RiemannianChartVolumeDensity RiemannianMapJacobian RiemannianSourceDensityIntegral
  RiemannianMapAreaJacobianMeasurable RiemannianPathLipschitz
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension PartialDensityProduct
  MeasureStepIntegralIdentification MeasureUP MeasurableFunctionUP MeasurableZeroExtension
  MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [riemannian_subset_source_volume_graph]:
    the exact subset product graph in the area formula
    of 3.2.46, p. 282. The total strictly positive
    volume density has no missing points outside the
    cut-off set; zero times that value remains zero. *)
Lemma riemannian_subset_source_volume_graph (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (S : set (riemannian_metric_space hg)) x z :
  partial_function_graph (partial_density_product
    (partial_function_zero_extension (0 : extended_real_line R) S (extended_riemannian_map_jacobian f m))
    (partial_function_total (fun x : riemannian_metric_space hg=>
      ((riemannian_chart_volume_density hg x)%:E : extended_real_line R)))) x z <->
  partial_function_graph (partial_function_zero_extension (0 : extended_real_line R) S
    (partial_real_function_embed (riemannian_map_euclidean_source_jacobian f m))) x z.
Proof.
case: (pselect (S x))=> hx.
- rewrite (partial_function_zero_extension_on _ _ _ hx) partial_density_product_graph.
  split.
  + move=> [j [d [hj [hd hValue]]]].
    apply: (@riemannian_map_extended_source_volume_graph R m n A B g h hg hh f x z).2.
    apply/partial_density_product_graph; exists j,d; split; last by split.
    exact: (partial_function_zero_extension_on _ _ _ hx).1 hj.
  + move=> /(@riemannian_map_extended_source_volume_graph R m n A B g h hg hh f x z)
      /partial_density_product_graph [j [d [hj [hd hValue]]]].
    exists j,d; split; last by split.
    exact: (partial_function_zero_extension_on _ _ _ hx).2 hj.
- rewrite (partial_function_zero_extension_off _ _ _ hx) partial_density_product_graph.
  split.
  + move=> [j [d [hj [hd hValue]]]].
    have hJ : j=0 := (partial_function_zero_extension_off _ _ _ hx).1 hj.
    by rewrite hJ mul0e in hValue; exact: esym hValue.
  + move=> ->.
    exists 0,(riemannian_chart_volume_density hg x)%:E; split.
    * apply/partial_function_zero_extension_graph; right; by split.
    * split; first by [].
      exact: mul0e.
Qed.

(** Source for [riemannian_subset_area_source_integral_iff]:
    the actual source metric and volume are restored
    on the original measurable S, supporting 3.2.46,
    p. 282. Measurability of the actual Jacobian is
    derived from original path-Lipschitz continuity. No
    coordinate, derivative-field or integrability hypothesis
    is added; both signed integral graphs are retained. *)
Theorem riemannian_subset_area_source_integral_iff (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : (0<=m%:R :> R)%R) (S : set (riemannian_metric_space hg)) :
  is_riemannian_path_lipschitz f ->
  measure_measurable (@riemannian_chart_reference R m A g hg) S -> forall a,
  is_measure_subset_integral (riemannian_hausdorff_measure hg m%:R hp) S
    (extended_riemannian_map_jacobian f m) a <->
  is_measure_subset_integral (@riemannian_chart_reference R m A g hg) S
    (partial_real_function_embed (riemannian_map_euclidean_source_jacobian f m)) a.
Proof.
move=> hLip hS a.
pose X := [the choiceType of riemannian_metric_space hg].
pose phi := @riemannian_chart_reference R m A g hg.
pose K := partial_function_zero_extension (0 : extended_real_line R) S
  (extended_riemannian_map_jacobian f m).
have hMeas := @measurable_zero_extension R X (extended_real_line R) phi
  (@riemannian_chart_reference_is_measure R m A g hg) 0 S
  (extended_riemannian_map_jacobian f m) hS
  (@extended_riemannian_map_area_jacobian_measurable R m n A B g h hg hh f hLip).
have hChange := @riemannian_source_density_integral_iff R m A g hg hp K hMeas a.
split=> hi.
- apply: (measure_integral_graph_equivalent _ (hChange.1 hi))=> x z.
  exact: (@riemannian_subset_source_volume_graph R m n A B g h hg hh f S x z).
- apply: hChange.2.
  apply: (measure_integral_graph_equivalent _ hi)=> x z.
  exact: (iff_sym (@riemannian_subset_source_volume_graph R m n A B g h hg hh f S x z)).
Qed.
