(** Federer (1969), 3.1.4, p. 214: scalar-coordinate reduction
    of measurability, using the countable-product criterion 2.3.2(5).
    A separate conull-domain law includes an empty target family. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanCoordinateTopology RealMetricBackground RealLineSeparability
  SeparableMetricBaseSealed PartialFunctionUP PartialFunctionPostcomposition
  MeasureUP MeasureAlmostUP MeasurableFunctionUP MeasurableCountableProducts
  MeasurablePostcomposition BorelFunctionBasic MeasurableGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory numFieldTopology.Exports ArrowAsProduct.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [measurable_euclidean_coordinate_criterion]: the
    finite-coordinate reduction in Federer 3.1.4, p. 214, applied
    to measurability, by 2.3.2(5), p. 73. Coordinates reconstruct
    the same partial graph, including its original missing domain. *)
Theorem measurable_euclidean_coordinate_criterion (R : realType) (X : choiceType) n
    (mu : set X -> \bar R) (f : partial_function X
      (inner_metric_space (@euclidean_inner_productP R n))) :
  is_measure mu -> measure_almost_everywhere mu (partial_function_domain f) ->
  (is_measure_measurable_function mu f <-> forall j : 'I_n,
    @is_measure_measurable_function R X [the topologicalType of real_line_metric R]
      mu (partial_function_postcompose f (fun v=>(v j : real_line_metric R)))).
Proof.
move=> hm hd; split.
- move=> hf j; apply: (measurable_function_borel_postcomposition hm hf).
  exact: continuous_borel_function (@euclidean_coordinate_continuous R n j).
- move=> hc.
  pose F := partial_function_postcompose f (fun v=>fun j : 'I_n=>(v j : R^o)).
  have [D [hDc hDd]] := real_line_countable_dense R.
  pose U := @SeparableMetricBase.value R [the metricType R of real_line_metric R] D hDc hDd.
  have hU := @SeparableMetricBase.laws R [the metricType R of real_line_metric R] D hDc hDd.
  have hFd : measure_almost_everywhere mu (partial_function_domain F).
    by rewrite /F partial_function_postcompose_domain.
  have hF : @is_measure_measurable_function R X
      [the topologicalType of ('I_n -> R^o)] mu F.
    apply: (@measurable_function_countable_product_iff R X [the choiceType of 'I_n]
      (fun _=>[the topologicalType of R^o]) mu hm F (fun _=>U)
      (countableP _) (fun _=>hU) hFd).2=> j.
    apply: (measurable_function_graph_equivalent _ (hc j))=> x y.
    split.
    + move=> [v [hv <-]]; exists (fun j=>v j); split=> //; by exists v.
    + by move=> [v [[w [hw <-]] <-]]; exists w.
  pose G (u : 'I_n -> R^o) : inner_metric_space (@euclidean_inner_productP R n) :=
    [ffun j=>u j].
  have hG : continuous G.
    apply: euclidean_map_continuous=> j.
    have he : (fun u : 'I_n -> R^o=>(G u j : R^o))=(fun u=>u j).
      by apply: funext=> u; rewrite /G ffunE.
    rewrite he; exact: proj_continuous.
  have hh := measurable_function_borel_postcomposition hm hF (continuous_borel_function hG).
  apply: (measurable_function_graph_equivalent _ hh)=> x y.
  split.
  + move=> [u [[v [hv <-]] <-]].
    have he : G (fun j=>v j)=v by apply/ffunP=> j; rewrite /G ffunE.
    by rewrite he.
  + move=> hy; exists (fun j=>y j); split; first by exists y.
    by apply/ffunP=> j; rewrite /G ffunE.
Qed.
