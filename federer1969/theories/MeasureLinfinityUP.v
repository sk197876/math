(** Federer (1969), 2.4.12, pp. 86–87: L-infinity membership and
    completeness. Partial domains follow Federer; the erratum's total-domain
    restriction applies to the separate vector-space/seminorm assertion. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP MeasurableNormedFunctionUP
  CountablyMeasurableUP MeasureEssentialNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_measure_linfinity_function]: direct p=infinity
    instance of Lp in Federer 2.4.12, p. 86:
    membership in A, finite essential norm, and countably
    measurable nonzero locus. No finite measure of X is imposed. *)
Definition is_measure_linfinity_function (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (f : partial_function X (real_norm_metric_space hN)) :=
  is_measurable_normed_function mu f /\
  measure_essential_norm mu N f < +oo /\
  is_countably_measure_measurable_function mu (0%R : real_norm_metric_space hN) f.
