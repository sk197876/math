(** Federer (1969), 2.10.28, p. 193: supporting zero Lebesgue measure of
    A(m,n) for 0<m<1. A finite fine interval cover of fixed total m-power
    cost has small total length. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground MetricDiameter CompactIntervalGauge CompactIntervalDiameter
  ConcaveIntervalGaugeUP SpecialIntervalFamilyUP RealPower RealPowerSuccessor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [fractional_power_length_bound]: supporting
    l<=delta^(1-m)*l^m for 0<=l<=delta
    in the nullity consequence of 2.10.28,
    p. 193. Zero lengths are included. *)
Lemma fractional_power_length_bound (R : realType) (m l delta : R) :
  0<m -> m<1 -> 0<=l -> l<=delta ->
  l<=real_power delta (1-m)*real_power l m.
Proof.
move=> hm hm1 hl hld.
case: (eqVneq l 0)=> [->|hl0]; first by rewrite real_power_zero_base ?gt_eqF // mulr0.
have hlp : 0<l by rewrite lt_neqAle eq_sym hl0 hl.
have hq : 0<1-m by lra.
have hh := @real_power_monotone R l delta (1-m) hl hld hq.
have hmul := ler_wpM2r (@real_power_nonnegative R l m) hh.
have hprod : real_power l (1-m)*real_power l m=l.
  rewrite -real_power_add_exponents_positive //.
  have he : 1-m+m = 1 by lra.
  by rewrite he real_power_one_exponent.
by rewrite hprod in hmul.
Qed.

(** Source for [power_special_family_length_sum_bound]: supporting
    sum diam(S)<=delta^(1-m) for a special
    family whose root has cost c, in the
    [0,1] construction of 2.10.28, p. 193.
    Its total m-power cost equals one after
    cancelling the positive normalising constant. *)
Theorem power_special_family_length_sum_bound (R : realType) (c m delta : R)
    (J : compact_real_intervals R) H :
  0<c -> 0<m -> m<1 ->
  is_special_interval_family (fun t=>c*real_power t m) J H ->
  concave_interval_cost (fun t=>c*real_power t m) (val J)=c ->
  (forall S, S \in H -> fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S))<=delta) ->
  \sum_(S <- H) fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S))<=
    real_power delta (1-m).
Proof.
move=> hc hm hm1 hH hJ hmesh.
pose len (S : compact_real_intervals R) :=
  fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S)).
have hcost := @special_interval_cost_sum R (fun t=>c*real_power t m) J H hH.
rewrite hJ /concave_interval_cost -mulr_sumr in hcost.
have hsum : (\sum_(S <- H) real_power (len S) m) = 1.
  have hc0 : c!=0 by rewrite gt_eqF.
  apply: (mulfI hc0); rewrite mulr1; exact: esym hcost.
have hbound : (\sum_(S <- H) len S)<=\sum_(S <- H) real_power delta (1-m)*real_power (len S) m.
  rewrite !big_seq; apply: ler_sum=> S hS.
  exact (@fractional_power_length_bound R m (len S) delta hm hm1
    (@compact_interval_diameter_nonnegative R (val S) (set_valP S)) (hmesh S hS)).
by rewrite -mulr_sumr hsum mulr1 in hbound.
Qed.
