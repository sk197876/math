(** Federer (1969), 2.4.15, proof p. 89: the real-valued factor |f+g|^(p-1)
    used in Holder's inequality. Supporting arbitrary positive powers are
    treated through the existing measurable norm-power laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormMetricScaleContinuity RealMetricBackground
  ExtendedRealOrderTopology ExtendedFiniteProjectionBorel PartialFunctionUP PartialFunctionPostcomposition
  PartialNormPower RealPower MeasurableNormPower MeasureUP MeasurableFunctionUP
  MeasurablePostcomposition MeasurableGraphEquivalence BorelFunctionUP BorelFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_scalar_norm_identity_continuous]: supporting
    topology identification for the real Holder factor in
    Federer 2.4.15, p. 89. Both scalar metrics
    are the absolute difference, so the identity is continuous. *)
Lemma real_scalar_norm_identity_continuous (R : realType) :
  continuous (fun x : real_line_metric R => (x : real_norm_metric_space (scalar_absolute_value_norm R))).
Proof.
apply: (@metric_fixed_lipschitz_continuous R _ _ _ 1%R ler01)=> x y.
change (is_true (`|x-y| <= 1 * `|x-y|)%R); by rewrite mul1r.
Qed.

(** Source for [partial_scalar_norm_power]: supporting real
    powered norm, used with exponent p-1 in Federer
    2.4.15, p. 89. It keeps the original
    partial domain and uses the scalar norm metric as target. *)
Definition partial_scalar_norm_power (R : realType) (X Y : Type)
    (N : Y -> R) (p : R) (f : partial_function X Y) :=
  partial_function_postcompose f (fun y => (real_power (N y) p : real_norm_metric_space (scalar_absolute_value_norm R))).

(** Source for [measurable_scalar_norm_power]: measurability of the real
    Holder factor in Federer 2.4.15, p. 89 The finite projection is applied
    only to finite powered norm values, so it changes neither values nor
    domains. *)
Lemma measurable_scalar_norm_power (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  (0 < p)%R -> is_measure_measurable_function mu f ->
  is_measure_measurable_function mu (partial_scalar_norm_power N p f).
Proof.
move=> hp hf.
have hpow := @measurable_norm_positive_power R X V N hN mu hm p f hp hf.
have hreal := @measurable_function_borel_postcomposition R X (extended_real_line R)
  [the topologicalType of real_line_metric R] mu hm _
  (fun y => (fine y : real_line_metric R)) hpow (@extended_finite_projection_borel R).
have hid : is_borel_function (fun x : real_line_metric R => (x : real_norm_metric_space (scalar_absolute_value_norm R))).
  apply: continuous_borel_function; exact: real_scalar_norm_identity_continuous.
have hscalar := @measurable_function_borel_postcomposition R X [the topologicalType of real_line_metric R]
  [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] mu hm _ _ hreal hid.
apply: (@measurable_function_graph_equivalent R X _ mu _ _ _ hscalar)=> x z; split.
- move=> [a [[b [[y [hy hyb]] hba]] haz]].
  exists y; split=> //; by rewrite -haz -hba -hyb.
- move=> [y [hy hyz]]; exists (real_power (N y) p); split=> //.
  exists (real_power (N y) p)%:E; split=> //; exists y; by split.
Qed.

(** Source for [scalar_norm_power_iterate_graph]: supporting identity
    (|f+g|^(p-1))^q=|f+g|^p when (p-1)q=p in Federer 2.4.15, p. 89 The graph
    law here permits arbitrary positive exponents. *)
Lemma scalar_norm_power_iterate_graph (R : realType) (X : Type)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N) (p q : R)
    (f : partial_function X V) x z :
  (0 < p)%R -> (0 < q)%R ->
  (partial_function_graph (partial_norm_power (fun a : R => `|a|%R) q (partial_scalar_norm_power N p f)) x z <->
   partial_function_graph (partial_norm_power N (p*q)%R f) x z).
Proof.
move=> hp hq.
have he y : real_power `|real_power (N y) p|%R q = real_power (N y) (p*q)%R.
  rewrite (ger0_norm (real_power_nonnegative _ _)).
  exact (@real_power_positive_iterate R (N y) p q (real_seminorm_nonnegative hN.1 y) hp hq).
split.
- move=> [a [[y [hy hya]] haz]]; exists y; split=> //.
  by rewrite -hya he in haz.
- move=> [y [hy hyz]]; exists (real_power (N y) p); split; first by exists y; split.
  by rewrite he.
Qed.
