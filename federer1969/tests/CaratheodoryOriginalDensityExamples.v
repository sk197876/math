(** Boundary regressions for the original partial quotient in Federer
    2.10.17(3), p. 179. Use the actual uncut envelope of the existing
    cost that vanishes on subsingletons. These are project regressions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureRestriction MeasureDerivates PartialFunctionUP
  MetricScaleEnvelope CaratheodoryDensityFunction CaratheodoryDensityQuotient
  CaratheodoryOriginalDensity SubsingletonCoverCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section Examples.
Variable R : realType.
Variable X : metricType R.
Local Notation F := (@setT (set X)).
Local Notation c := (@subsingleton_cover_cost R X).
Local Notation omega := (metric_scale_envelope
  (fun j : set_type F => val j) (fun j => c (val j)) +oo).

(** Source for [uncut_free_singleton_mass_zero]: concrete generator
    regression for Federer 2.10.17(3), p. 179. The actual uncut envelope
    of the subsingleton cost has mass zero on a singleton, even when the
    ambient space and its total measure are infinite. *)
Theorem uncut_free_singleton_mass_zero (a : X) : omega [set a]=0.
Proof.
have hz := @uncut_caratheodory_zero_cost_restriction R X F c omega setT
  (fun S _ => subsingleton_cover_cost_nonnegative R S)
  (metric_scale_envelope_specification _ _ _) [set a] I
  (subsingleton_cover_cost_singleton R a).
by rewrite setTI in hz.
Qed.

(** Source for [uncut_free_singleton_original_domain]: domain regression
    for Federer 2.10.17(3), p. 179. Its original partial quotient remains
    undefined at the free singleton, whereas the auxiliary filled
    quotient has value zero there. The new theorem does not redefine
    the original quotient or extend the global arithmetic of 2.1.1. *)
Theorem uncut_free_singleton_original_domain (a : X) :
    ~ partial_function_domain
      (measure_ratio_function (measure_restrict omega setT) c) [set a] /\
    partial_function_graph (caratheodory_density_function omega c setT) [set a] 0.
Proof.
split.
- apply: measure_ratio_zero_denominator.
  exact: subsingleton_cover_cost_singleton.
- rewrite caratheodory_density_function_graph setTI
    uncut_free_singleton_mass_zero (subsingleton_cover_cost_singleton R a).
  exact: caratheodory_density_divide_zero_zero.
Qed.
End Examples.
