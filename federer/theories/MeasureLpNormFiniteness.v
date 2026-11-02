(** Federer (1969), 2.4.12, pp. 86–87: the norm superlevel estimate and
    redundancy of countable measurability for finite p. The proofs use
    characteristic lower functions and the project's own integral laws; no
    external Markov or Lp theorem is imported. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower MeasureUP MeasurableFunctionUP
  MeasureIntegralBounds MeasureIntegralUniqueness MeasureNonnegativeLowerIntegral ExtendedPositivePower
  MeasureLpNormUP MeasureLpNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lp_norm_lower_integral]: the defining
    formula of Federer 2.4.12, p. 86, recovered from
    the abstract norm specification and uniqueness of the integral. *)
Lemma measure_lp_norm_lower_integral (R : realType) (X : choiceType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (mu : set X -> \bar R)
    (p : R) (f : partial_function X (real_norm_metric_space hN)) :
  is_measure mu -> (1 <= p)%R -> is_measure_measurable_function mu f ->
  measure_lp_norm mu N p f =
    extended_positive_power (measure_lower_integral mu (partial_norm_power N p f)) p^-1.
Proof.
move=> hm hp hf; have [_ [b [hb he]]] := (@measure_lp_norm_specification R X V N hN mu p f hm hp hf).
have eb := measure_lower_integral_unique hb.2.2 (measure_lower_integral_specification mu _).
by rewrite he eb.
Qed.

(** Source for [measure_lp_norm_finite_iff]: supporting equivalence
    of finite norm and finite integral of |f|^p in Federer
    2.4.12, p. 86, for finite p. *)
Lemma measure_lp_norm_finite_iff (R : realType) (X : choiceType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (mu : set X -> \bar R)
    (p : R) (f : partial_function X (real_norm_metric_space hN)) :
  is_measure mu -> (1 <= p)%R -> is_measure_measurable_function mu f ->
  (measure_lp_norm mu N p f < +oo) =
    (measure_lower_integral mu (partial_norm_power N p f) < +oo).
Proof.
move=> hm hp hf; rewrite measure_lp_norm_lower_integral //.
apply: extended_positive_power_finite_iff.
- apply: (@measure_lower_integral_nonnegative R X mu hm).
  exact: (@partial_norm_power_almost_nonnegative R X (real_norm_metric_space hN) mu hm N p f (measurable_function_domain hf)).
- rewrite invr_gt0; exact: lt_le_trans (ltr01) hp.
Qed.
