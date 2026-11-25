(** Federer (1969), 2.4.17, p. 90: P is a subinterval of the extended real
    line. The order specification below includes empty sets and singletons,
    including the singleton {infinity}; it requires every point between two
    members to belong. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP MeasureUP MeasurableFunctionUP
  MeasureExponentDomain MeasureLpExponentInterval MeasureLpInfinityInterval.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_extended_real_interval]: the subinterval
    condition in the first assertion of Federer 2.4.17, p. 90,
    including the possible endpoint infinity. *)
Definition is_extended_real_interval (R : realType) (P : set (\bar R)) :=
  forall s t p, P s -> P t -> s <= p -> p <= t -> P p.

(** Source for [measure_finite_norm_exponents_interval]: complete
    first assertion of Federer 2.4.17, p. 90: P is a
    subinterval of the extended real line. No countable-measurability
    premise or positive-measure assumption is added. *)
Theorem measure_finite_norm_exponents_interval (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  is_measure_measurable_function mu f ->
  is_extended_real_interval (measure_finite_norm_exponents mu f).
Proof.
move=> hf s t p [hs hsf] [ht htf] hsp hpt; split; first exact: le_trans hs hsp.
case: s hs hsf hsp=> [s| |] hs hsf hsp; last by move: hs; rewrite leNgt ltNyr.
- case: p hsp hpt=> [p| |] hsp hpt; last by move: hsp; rewrite leNgt ltNyr.
  + case: t ht htf hpt=> [t| |] ht htf hpt; last by move: hpt; rewrite leNgt ltNyr.
    * exact: (@measure_lp_finite_exponents_interval R X R^o _ (scalar_absolute_value_norm R)
        mu hm s p t f hs hsp hpt hf hsf htf).
    * exact: (@measure_lp_infinity_exponent_interval R X R^o _ (scalar_absolute_value_norm R)
        mu hm s p f hs hsp hf hsf htf).
  + have he : t=+oo by apply/eqP; rewrite eq_le leey hpt.
    by rewrite he in htf.
- have he : p=+oo by apply/eqP; rewrite eq_le leey hsp.
  by rewrite he.
Qed.
