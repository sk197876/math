(** Federer (1969), 2.10.28, p. 193: A(m,n) has zero scalar Lebesgue measure
    for 0<m<1, so the derivative assertion off A holds almost everywhere.
    Prove nullity from fine level covers and their conserved power cost,
    without assuming a dimension theorem. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground MetricDiameter MetricDiameterReal CompactIntervalGauge
  CompactIntervalDiameter PowerConcaveIntervalGauge PowerIntervalLengthBound RealPower RealPowerContinuity
  SpecialIntervalFamilyUP SpecialIntervalTreeLevels MeasureUP MeasureBasic MeasureIndexedCover
  NonnegativeSum LebesgueScalarMeasure ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [power_interval_tree_limit_lebesgue_null]: direct
    Lebesgue nullity of the [0,1] power-gauge
    limit used in the final almost-everywhere
    sentence of 2.10.28, p. 193. The
    proof works for any special tree of
    that root, not just equal-cost refinements. *)
Theorem power_interval_tree_limit_lebesgue_null (R : realType) (c m : R)
    (J : compact_real_intervals R) H A :
  0<c -> 0<m -> m<1 -> val J=(`[0,1] : set (real_line_metric R)) ->
  H 0%N=[fset J] -> is_special_interval_tree (fun t=>c*real_power t m) H ->
  is_special_interval_tree_limit H A -> lebesgue_scalar_measure A=0%E.
Proof.
move=> hc hm hm1 hJ hroot ht hA.
have hg := @power_concave_interval_gauge R c m hc hm hm1.
have hlevels := @special_interval_tree_level_special R _ hg H ht J hroot.
have hJcost : concave_interval_cost (fun t=>c*real_power t m) (val J)=c.
  by rewrite hJ (concave_interval_cost_segment _ ler01) subr0 real_power_one_base mulr1.
have hq : 0<1-m by lra.
have hnon := @measure_nonnegative R R (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) A.
apply/eqP; rewrite eq_le hnon andbT.
apply: (@extended_upper_bound_from_scaled_errors R (lebesgue_scalar_measure A) 0 1 (@ler01 R))=> e he.
rewrite mul1r add0r.
have [d hd hnear] := @real_power_local_bound R 0 (1-m) e (lexx 0) hq he.
pose delta := d/2.
have hdelta : 0<delta by rewrite /delta divr_gt0 // ltr0n.
have hdeltaSmall : `|0-delta|<d by rewrite sub0r normrN ger0_norm // /delta; lra.
have hpow := hnear delta (ltW hdelta) hdeltaSmall.
rewrite real_power_zero_base ?gt_eqF // sub0r normrN in hpow.
have hpowSmall : real_power delta (1-m)<e.
  by rewrite ger0_norm ?real_power_nonnegative in hpow.
have [N hmesh] := @special_tree_mesh R _ H ht delta hdelta.
have hlen := @power_special_family_length_sum_bound R c m delta J (H N) hc hm hm1
  (hlevels N) hJcost (fun S hS=>hmesh N (leqnn N) S hS).
have hcover : A `<=` \bigcup_(S in [set S : compact_real_intervals R | S \in H N]) val S.
  move=> x hx; have [S [hS hxS]] := (hA x).1 hx N; by exists S.
have hmeasure := @measure_indexed_cover R R (compact_real_intervals R) (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) A [set S | S \in H N] (fun S=>val S)
  (finite_set_countable (finite_fset (H N))) hcover.
rewrite (@nonnegative_sum_finite R (compact_real_intervals R) (H N)
  (fun S=>lebesgue_scalar_measure (val S))
  (fun S _=>measure_nonnegative (lebesgue_scalar_is_measure R) (val S))) in hmeasure.
have heq (S : compact_real_intervals R) : lebesgue_scalar_measure (val S)=
    (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S)))%:E.
  have [a [b [hab hS]]] := set_valP S.
  by rewrite hS (lebesgue_scalar_segment hab) (extended_metric_diameter_segment hab).
have hsum : (\sum_(S <- H N) lebesgue_scalar_measure (val S))=
    (\sum_(S <- H N) fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S)))%:E.
  rewrite -sumEFin; by apply: eq_big_seq=> S hS; rewrite heq.
rewrite hsum in hmeasure.
have hfinal : ((\sum_(S <- H N) fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S)))%:E<=e%:E)%E.
  rewrite lee_fin; exact: le_trans hlen (ltW hpowSmall).
exact: le_trans hmeasure hfinal.
Qed.
