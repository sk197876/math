(** Federer (1969), 2.4.12, p. 86: the finite-p norm formula exposed through
    its abstract integral-root laws. Source context and conventions:
    MeasureLpNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower MeasureUP MeasurableFunctionUP
  ExtendedPositivePower MeasureIntegralUP MeasureIntegralUniqueness MeasureLpNormUP MeasureLpNormSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lp_norm]: the public finite-p value
    in Federer 2.4.12, p. 86; downstream proofs use
    the sealed characterisation, not the witness construction. *)
Definition measure_lp_norm (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (N : Y -> R) (p : R) (f : partial_function X Y) :=
  MeasureLpNorm.value mu N p f.

(** Source for [measure_lp_norm_specification]: the integral-root
    specification in Federer 2.4.12, p. 86. *)
Lemma measure_lp_norm_specification (R : realType) (X : choiceType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (mu : set X -> \bar R)
    (p : R) (f : partial_function X (real_norm_metric_space hN)) :
  is_measure mu -> (1 <= p)%R -> is_measure_measurable_function mu f ->
  is_measure_lp_norm mu N p f (measure_lp_norm mu N p f).
Proof. exact: MeasureLpNorm.laws. Qed.

(** Source for [measure_lp_norm_of_integral]: evaluating the
    finite-p norm from any proved integral value, as in the
    defining formula of Federer 2.4.12, p. 86. *)
Lemma measure_lp_norm_of_integral (R : realType) (X : choiceType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (mu : set X -> \bar R)
    (p : R) (f : partial_function X (real_norm_metric_space hN)) b :
  is_measure mu -> (1 <= p)%R -> is_measure_measurable_function mu f ->
  is_measure_integral mu (partial_norm_power N p f) b ->
  measure_lp_norm mu N p f = extended_positive_power b p^-1.
Proof.
move=> hm hp hf hb; apply: measure_lp_norm_unique ((@measure_lp_norm_specification R X V N hN mu p f hm hp hf)) _.
split=> //; exists b; by split.
Qed.

(** Source for [measure_lp_norm_nonnegative]: sign of the
    finite-p norm in Federer 2.4.12, p. 86. *)
Lemma measure_lp_norm_nonnegative (R : realType) (X : choiceType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (mu : set X -> \bar R)
    (p : R) (f : partial_function X (real_norm_metric_space hN)) :
  is_measure mu -> (1 <= p)%R -> is_measure_measurable_function mu f ->
  0 <= measure_lp_norm mu N p f.
Proof.
move=> hm hp hf; have [_ [b [_ ->]]] := (@measure_lp_norm_specification R X V N hN mu p f hm hp hf).
exact: extended_positive_power_nonnegative.
Qed.
