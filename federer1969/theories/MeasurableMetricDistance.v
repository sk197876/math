(** Federer (1969), 2.3.7, pp. 77–78: measurable distance comparisons.
    Source context: UniformPartialConvergenceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialFunctionPair
  PartialFunctionPostcomposition MeasureUP MeasurableFunctionUP MeasurablePairs
  MeasurablePostcomposition MeasurableFunctionBorel BorelFunctionBasic TopologicalBorel
  CountableOpenBaseUP SeparableMetricBaseSealed CountableOrderIntervals MetricPairDistance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [partial_metric_distance]: supporting partial
    distance map in the defining sets C_{i,j} of Federer 2.3.7,
    p. 77. Its domain is exactly the two inputs' common domain. *)
Definition partial_metric_distance (R : realType) (X : Type) (Y : metricType R)
    (f g : partial_function X Y) :=
  partial_function_postcompose (partial_function_pair f g)
    (fun p => (mdist p.1 p.2 : real_line_metric R)).

(** Source for [measurable_partial_metric_distance]: supporting
    measurability of the distances in Federer 2.3.7, pp. 77–78 Separability
    supplies the countable coordinate bases for the product theorem of
    2.3.2(5). *)
Lemma measurable_partial_metric_distance (R : realType) (X : choiceType)
    (Y : metricType R) (mu : set X -> \bar R) (hm : is_measure mu)
    (D : set Y) (f g : partial_function X Y) : countable D -> dense D ->
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  is_measure_measurable_function mu (partial_metric_distance f g).
Proof.
move=> hc hd hf hg; pose U := @SeparableMetricBase.value R Y D hc hd.
have hU := @SeparableMetricBase.laws R Y D hc hd.
apply: (@measurable_function_borel_postcomposition R X (Y * Y)%type (real_line_metric R) mu hm).
- exact (@measurable_partial_function_pair R X Y Y nat nat mu hm f g U U
    (countable_base_open hU) (countable_base_refines hU)
    (countable_base_open hU) (countable_base_refines hU) hf hg).
- apply: continuous_borel_function; exact: metric_pair_distance_continuous.
Qed.

(** Source for [partial_metric_deviation_set]: supporting single
    deviation set {x: distance(f_n(x),g(x)) >= eta} in
    Federer 2.3.7, p. 77. Undefined values are not included. *)
Definition partial_metric_deviation_set (R : realType) (X : Type)
    (Y : metricType R) (f g : partial_function X Y) (eta : R) : set X :=
  [set x | exists y z, partial_function_graph f x y /\ partial_function_graph g x z /\ eta <= mdist y z].

(** Source for [partial_metric_deviation_preimage]: supporting inverse-image
    identity for the sets used in Federer 2.3.7, pp. 77–78 *)
Lemma partial_metric_deviation_preimage (R : realType) (X : Type)
    (Y : metricType R) (f g : partial_function X Y) eta :
  partial_metric_deviation_set f g eta =
  partial_function_preimage (partial_metric_distance f g) [set t | eta <= t].
Proof.
apply/seteqP; split=> x.
- move=> [y [z [hy [hz he]]]]; exists (mdist y z); split=> //.
  exists (y,z); split; first by split.
  by [].
- move=> [t [[p [[hy hz] hp]] he]]; exists p.1, p.2; split=> //; split=> //.
  by rewrite hp.
Qed.

(** Source for [partial_metric_deviation_measurable]: measurable
    single deviation sets in Federer 2.3.7, pp. 77–78.
    This statement applies at every real threshold, including zero. *)
Lemma partial_metric_deviation_measurable (R : realType) (X : choiceType)
    (Y : metricType R) (mu : set X -> \bar R) (hm : is_measure mu)
    (D : set Y) (f g : partial_function X Y) eta : countable D -> dense D ->
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  measure_measurable mu (partial_metric_deviation_set f g eta).
Proof.
move=> hc hd hf hg; rewrite partial_metric_deviation_preimage.
apply: (@measurable_function_borel_preimage R X (real_line_metric R) mu hm _
  (@measurable_partial_metric_distance R X Y mu hm D f g hc hd hf hg)).
apply: closed_borel_set; exact: order_closed_upper_ray_closed.
Qed.
