(** Federer (1969), 2.10.28, p. 191: compact interval power costs give the
    real-line power-gauge measure. Combine both independently proved cover
    comparisons, with the positive coefficient explicit. This connects the
    established power Cantor pair to the real-degree measure needed in
    2.10.29, pp. 193–195. Euler-Gamma normalisation remains separate. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground RealPower MetricRealPowerMeasure MetricRealPowerIntervalUpper
  MetricRealPowerIntervalLower ConcaveIntervalMeasure PowerCantorPairUP PowerCantorPair
  FiniteCumulativeFunctionUP MeasureRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_real_power_interval_measure_agreement]: direct
    interval-generated power-measure identification
    in 2.10.28, p. 191, including degree
    zero and the supporting zero-coefficient case.
    Equality holds on every subset, without
    a measurability or boundedness premise. *)
Theorem metric_real_power_interval_measure_agreement (R : realType) (c p : R) :
  0<=c -> 0<=p -> forall A : set (real_line_metric R),
    @metric_real_power_measure R [the metricType R of real_line_metric R] c p A=
    concave_interval_measure (fun x=>c*real_power x p) A.
Proof.
move=> hc hp A; apply/eqP; rewrite eq_le.
by rewrite (@metric_real_power_below_interval_measure R c p hc hp A)
  (@interval_measure_below_metric_real_power R c p hc hp A).
Qed.

(** Source for [power_cantor_pair_real_power_mass]: direct
    mass c of A(m,n) in 2.10.28,
    p. 193, for the unrestricted real
    diameter power-gauge measure. The actual
    equality with compact interval covers has
    now been proved; the normalising coefficient
    c remains explicit. *)
Theorem power_cantor_pair_real_power_mass (R : realType) (c m : R) n A f :
  0<c -> 0<m -> m<1 -> is_power_cantor_pair c m n A f ->
  @metric_real_power_measure R [the metricType R of real_line_metric R] c m A=c%:E /\
  forall x : R,
    @metric_real_power_measure R [the metricType R of real_line_metric R] c m (A `&` [set z | z<=x])=(f x)%:E.
Proof.
move=> hc hm hm1 hpair.
have hp := @power_cantor_pair_properties R c m n A f hc hm hm1 hpair.
split.
- rewrite (@metric_real_power_interval_measure_agreement R c m (ltW hc) (ltW hm) A).
  exact hp.2.2.1.
- move: hpair=> [J [H [hJ [ht [hA hf]]]]].
  move=> x; rewrite (@metric_real_power_interval_measure_agreement R c m (ltW hc) (ltW hm)).
  exact (hf x).
Qed.
