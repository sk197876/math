(** Federer (1969), 2.4.12, p. 86: the finite-p integral-root formula. These
    modules retain the possibly infinite value and exact partial domain. The
    abstract specification precedes its witness and sealed interface.
    Seminorm and completeness laws are separate results, not assumptions
    included in this specification. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower MeasurableNormPower
  MeasureUP MeasurableFunctionUP MeasureIntegralBounds MeasureNonnegativeIntegral
  ExtendedPositivePower MeasureLpNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lp_norm_witness]: private witness for
    the finite-p formula of Federer 2.4.12, p. 86.
    The lower integral supplies the common integral value by
    2.4.4(2); its characterisation is proved below. *)
Definition measure_lp_norm_witness (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (N : Y -> R) (p : R) (f : partial_function X Y) :=
  extended_positive_power (measure_lower_integral mu (partial_norm_power N p f)) p^-1.

(** Source for [measure_lp_norm_witness_laws]: existence proof
    for the finite-p definition of Federer 2.4.12, p. 86,
    including infinite integrals. No finite-dimensional target
    or finite-measure source assumption is required. *)
Lemma measure_lp_norm_witness_laws (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R -> is_measure_measurable_function mu f ->
  is_measure_lp_norm mu N p f (measure_lp_norm_witness mu N p f).
Proof.
move=> hp hf; split=> //.
exists (measure_lower_integral mu (partial_norm_power N p f)); split=> //.
have hpos : (0 < p)%R := lt_le_trans (ltr01) hp.
have hmeas := measurable_norm_positive_power hm hpos hf.
have hnonneg := (@partial_norm_power_almost_nonnegative R X (real_norm_metric_space hN) mu hm N p f (measurable_function_domain hf)).
exact: (nonnegative_measurable_function_integral hm hmeas hnonneg).1.
Qed.
