(** Federer (1969), 2.4.14, p. 88: scaling the functions before the
    application of weighted arithmetic and geometric means. The same
    identities support Lp homogeneity in Federer 2.4.12, p. 87. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormMetricScaleContinuity RealPower
  PartialFunctionUP PartialNormedArithmetic PartialNormPower PartialFunctionBasic MeasureUpperIntegralScale
  MeasureUP MeasurableFunctionUP MeasurablePostcomposition BorelFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_normed_scalar_multiple]: supporting
    measurability of the scaled integrands in Federer 2.4.14,
    p. 88. Essential separability is unnecessary for this
    individual closure statement. *)
Lemma measurable_normed_scalar_multiple (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (c : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  is_measure_measurable_function mu f ->
  is_measure_measurable_function mu (partial_vector_scale c f).
Proof.
move=> hf; apply: (@measurable_function_borel_postcomposition R X
  [the topologicalType of real_norm_metric_space hN]
  [the topologicalType of real_norm_metric_space hN] mu hm f (fun y => c *: y) hf).
apply: continuous_borel_function; exact: real_norm_metric_scale_continuous.
Qed.

(** Source for [partial_norm_power_scaled_graph]: exact graph
    identity behind the normalisation in Federer 2.4.14,
    p. 88, and homogeneity in 2.4.12, p. 87.
    The scalar may be zero; both sides keep precisely the
    original partial domain. *)
Lemma partial_norm_power_scaled_graph (R : realType) (X : Type)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (f : partial_function X V) (c p : R) x z :
  partial_function_graph (partial_norm_power N p (partial_vector_scale c f)) x z <->
  partial_function_graph (partial_extended_function_scale (real_power `|c| p)
    (partial_norm_power N p f)) x z.
Proof.
have he y : (real_power (N (c *: y)) p)%:E =
    (real_power `|c| p)%:E * (real_power (N y) p)%:E.
  by rewrite (real_seminorm_scale hN.1)
    (@real_power_product R `|c| (N y) p (normr_ge0 c) (real_seminorm_nonnegative hN.1 y)) EFinM.
split.
- move=> [y [[a [ha hay]] hyz]].
  exists (real_power (N a) p)%:E; split; first by exists a; split.
  by rewrite -he hay.
- move=> [w [[a [ha haw]] hwz]].
  exists (c *: a)%R; split; first by exists a; split.
  by rewrite he haw.
Qed.
