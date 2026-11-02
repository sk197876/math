(** Federer (1969), 2.10.2(1), p. 171: measure and closed-cover regularity
    consequences of the abstract real power-gauge specification. The
    positive normalising coefficient is explicit; no Euler-Gamma identity is
    assumed. These supporting laws are used in 2.10.29, pp. 193–195. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MetricRealPowerCost MetricRealPowerMeasureUP
  CaratheodoryLimitMeasure CaratheodoryBorelRegular MeasureUP TopologicalBorel BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_real_power_measure_law]: direct
    measure assertion for the real power gauge
    of 2.10.2(1), p. 171, from 2.10.1.
    Nonnegativity of the coefficient suffices
    for this supporting measure consequence. *)
Lemma metric_real_power_measure_law (R : realType) (X : metricType R) (c p : R)
    (mu : set X -> \bar R) :
  0<=c -> is_metric_real_power_measure c p mu -> is_measure mu.
Proof.
move=> hc hm; apply: (caratheodory_limit_is_measure hm)=> S.
exact (@metric_real_power_cost_nonnegative R c p _ hc).
Qed.

(** Source for [closed_metric_real_power_measure_law]: direct
    measure assertion for the independent closed
    covering family of 2.10.2(1), p. 171. *)
Lemma closed_metric_real_power_measure_law (R : realType) (X : metricType R) (c p : R)
    (mu : set X -> \bar R) :
  0<=c -> is_closed_metric_real_power_measure c p mu -> is_measure mu.
Proof.
move=> hc hm; apply: (caratheodory_limit_is_measure hm)=> S.
exact (@metric_real_power_cost_nonnegative R c p _ hc).
Qed.

(** Source for [closed_metric_real_power_borel_regular_law]: direct Borel
    regularity of the closed-cover version in 2.10.2(1), p. 171 Use the
    Borel-generator consequence of 2.10.1. *)
Lemma closed_metric_real_power_borel_regular_law (R : realType) (X : metricType R) (c p : R)
    (mu : set X -> \bar R) :
  0<=c -> is_closed_metric_real_power_measure c p mu -> is_borel_regular_measure mu.
Proof.
move=> hc hm; apply: (caratheodory_limit_borel_regular hm).
- move=> S; exact (@metric_real_power_cost_nonnegative R c p _ hc).
- move=> S; apply: closed_borel_set; exact: (set_valP S).1.
Qed.
