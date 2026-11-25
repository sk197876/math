(** Federer (1969), 2.4.12, pp. 86–87: the norm superlevel estimate and
    redundancy of countable measurability for finite p. The proofs use
    characteristic lower functions and the project's own integral laws; no
    external Markov or Lp theorem is imported. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower RealPower
  MeasureUP MeasurableFunctionUP MeasurableNormSuperlevels MeasureGauge MeasureIntegralBounds
  MeasureNonnegativeThresholdBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_norm_power_superlevel_bound]: direct
    inequality r^p mu{|f|>r} <= integral |f|^p in
    Federer 2.4.12, p. 87. The inequality already
    holds for every measurable f, including infinite integrals;
    the book applies it to members of Lp. *)
Theorem measure_norm_power_superlevel_bound (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p r : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  (0 < p)%R -> (0 <= r)%R -> is_measure_measurable_function mu f ->
  (real_power r p)%:E * mu (partial_norm_superlevel N f r%:E) <=
    measure_lower_integral mu (partial_norm_power N p f).
Proof.
move=> hp hr hf.
apply: (@nonnegative_threshold_lower_integral_bound R X mu hm _ _ _
  (measurable_norm_superlevel hm hf r) (real_power_nonnegative r p)).
- move=> x [y [hy hry]]; exists (real_power (N y) p)%:E; split.
  + exists y; by split.
  + rewrite lee_fin; apply: real_power_monotone hr _ hp.
    have h : (r < N y)%R := hry; exact: ltW h.
- exact: (@partial_norm_power_almost_nonnegative R X (real_norm_metric_space hN) mu hm N p f (measurable_function_domain hf)).
Qed.
