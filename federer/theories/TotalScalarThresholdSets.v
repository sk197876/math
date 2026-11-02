(** Federer (1969), 2.3.2(1), p. 73: open and closed inverse images of
    measurable functions are measurable. The scalar threshold sets below
    support the density-level tests in 2.5.10, p. 101. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureFiniteClosure MeasurableFunctionUP TotalScalarLpUP
  TotalScalarMeasurability CountableOrderIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [total_scalar_strict_upper_measurable]:
    strict scalar superlevel sets from Federer 2.3.2,
    p. 73, used for the threshold test of a
    putative density in 2.5.10, p. 101. *)
Lemma total_scalar_strict_upper_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> R) (c : R) :
  @is_measure_measurable_function R X
    [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)]
    mu (total_scalar_function f) ->
  measure_measurable mu [set x | c<f x].
Proof.
move=> hf; have hr := @total_scalar_real_measurable R X mu hm f hf.
have ho : @open [the topologicalType of real_line_metric R] [set y | c<y].
  exact: order_strict_upper_ray_open.
have hi := measurable_function_open_preimage hr ho.
have he : partial_function_preimage (partial_function_total (f : X -> real_line_metric R)) [set y | c<y]=[set x | c<f x].
  apply/seteqP; split=> x.
  - by move=> [y [<- hy]].
  - move=> hx; exists (f x); by split.
by rewrite he in hi.
Qed.

(** Source for [total_scalar_closed_lower_measurable]:
    closed scalar sublevel sets from Federer 2.3.2(1),
    p. 73, used in the horizontal-line comparison
    in 2.5.10, p. 101. *)
Lemma total_scalar_closed_lower_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> R) (c : R) :
  @is_measure_measurable_function R X
    [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)]
    mu (total_scalar_function f) ->
  measure_measurable mu [set x | f x<=c].
Proof.
move=> hf; have hi := measure_measurable_complement (@total_scalar_strict_upper_measurable R X mu hm f c hf).
have he : ~` [set x | c<f x]=[set x | f x<=c].
  apply/seteqP; split=> x hx.
  - change (f x <= c); rewrite leNgt; apply/negP; exact hx.
  - change (is_true (f x <= c)) in hx; move=> hn; have hn' : c<f x := hn.
    by move: hn'; rewrite ltNge hx.
by rewrite he in hi.
Qed.
