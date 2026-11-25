(** Federer (1969), 2.4.12, p. 86: the finite-p norm formula exposed through
    its abstract integral-root laws. Source context and conventions:
    MeasureLpNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP MeasurableNormedFunctionUP
  CountablyMeasurableUP MeasureLpNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_measure_lp_function]: direct finite-p membership
    definition in Federer 2.4.12, p. 86 Countable measurability is retained
    as printed; its redundancy for finite p is a theorem proved separately. *)
Definition is_measure_lp_function (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (p : R) (f : partial_function X (real_norm_metric_space hN)) :=
  (1 <= p)%R /\ is_measurable_normed_function mu f /\
  measure_lp_norm mu N p f < +oo /\
  is_countably_measure_measurable_function mu (0%R : real_norm_metric_space hN) f.
