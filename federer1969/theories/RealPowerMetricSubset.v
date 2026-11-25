(** Federer (1969), 3.2.46, p. 281: supporting ambient/subspace
    equality for real-dimensional Hausdorff measures on local metric
    patches. Prove it from actual covering infima, without assuming that
    completions of different ambient measures are interchangeable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import MetricSubsetBackground MetricDiameterUP MetricDiameter
  HausdorffLengthUP HausdorffMetricSubset MetricRealPowerCost
  MetricRealPowerMeasureUP MetricRealPowerMeasure RealPower RealPowerPositiveLipschitz
  LipschitzUP MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleCutoffCost
  MetricScaleMeasureBound CaratheodoryLimitUP MeasureUP MeasureBasic
  MeasurePushforward NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_real_power_metric_subset_measure]: supporting
    ambient/subspace equality in the local real-degree comparison of
    Federer 3.2.46, p. 281, expanding 2.10.26, pp. 189--190. The
    actual opaque real-power measures with the same coefficient occur
    on both sides, including infinite masses and
    arbitrary nonmeasurable subsets. *)
Theorem metric_real_power_metric_subset_measure (R : realType) (Y : metricType R)
    (K : set Y) (c p : R) (B : set (metric_subset K)) :
  (0<=c)%R -> (0<=p)%R ->
  @metric_real_power_measure R Y c p ((fun x : metric_subset K=>(val x : Y)) @` B)=
    @metric_real_power_measure R [the metricType R of metric_subset K] c p B.
Proof.
move=> hc hp.
pose X := [the metricType R of metric_subset K].
pose v := fun x : X=>(val x : Y).
have hv : is_metric_lipschitz_bound setT v 1%R.
  split; first exact: ler01.
  by move=> x z _ _; rewrite metric_subset_distanceE mul1r.
have hupper := @metric_real_power_positive_lipschitz R X Y v 1%R c p ltr01 hc hp hv B.
rewrite real_power_one_base mul1e in hupper.
apply/eqP; rewrite eq_le hupper /=.
apply: (caratheodory_limit_least (@metric_real_power_measure_specification R X c p))=> delta nu hd hn.
have hnu := metric_scale_envelope_is_measure hn
  (fun j=>@metric_real_power_cost_nonnegative R c p (extended_metric_diameter (val j)) hc).
pose xi := @metric_scale_envelope R Y (@nonempty_metric_sets R Y) (fun j=>val j)
  (fun j=>metric_real_diameter_cost c p (val j)) delta.
have hxi := @metric_scale_envelope_specification R Y (@nonempty_metric_sets R Y)
  (fun j=>val j) (fun j=>metric_real_diameter_cost c p (val j)) delta.
have hgen (j : @nonempty_metric_sets R Y) : extended_metric_diameter (val j)<=delta ->
    measure_pushforward v nu (val j)<=metric_real_diameter_cost c p (val j).
  move=> hj; rewrite /measure_pushforward.
  pose C := v @^-1` val j.
  change (is_true (nu C<=metric_real_diameter_cost c p (val j))).
  have hdiam : extended_metric_diameter C<=extended_metric_diameter (val j).
    exact: metric_subset_preimage_diameter_bound.
  case: (pselect (C!=set0))=> [hC|hC].
  - pose i : @nonempty_metric_sets R X := Sub C (mem_set hC).
    have hsize (s : @nonempty_metric_sets R X) (hs : [set i] s) : extended_metric_diameter (val s)<=delta.
      rewrite (hs : s = i); exact: le_trans hdiam hj.
    have hCover : C `<=` \bigcup_(s in [set i]) val s by move=> x hx; exists i.
    have hh := @metric_scale_envelope_lower R X (@nonempty_metric_sets R X)
      (fun s=>val s) (fun s=>metric_real_diameter_cost c p (val s)) delta nu hn C [set i]
      (countable1 i) hsize hCover.
    rewrite nonnegative_sum_singleton in hh; last exact: (@metric_real_power_cost_nonnegative R c p _ hc).
    apply: le_trans hh _; rewrite /metric_real_diameter_cost.
    exact: metric_real_power_cost_monotone hc hp (metric_diameter_nonnegative
      (extended_metric_diameter_specification C)) hdiam.
  - have he : C=set0.
      apply/seteqP; split=> [x hx|x []]; exfalso; apply: hC; by exists x.
    rewrite he (measure_empty hnu); exact: (@metric_real_power_cost_nonnegative R c p _ hc).
have hh := @measure_bounded_by_metric_scale_envelope R Y (@nonempty_metric_sets R Y)
  (fun j=>val j) (fun j=>metric_real_diameter_cost c p (val j)) delta xi (measure_pushforward v nu)
  hxi (measure_pushforward_is_measure v hnu) hgen (v @` B).
have he : v @^-1` (v @` B)=B.
  apply/seteqP; split=> [x [z hz heq]|x hx]; last by exists x.
  have ezx : z=x := val_inj heq; by rewrite -ezx.
rewrite /measure_pushforward he in hh.
apply: le_trans hh _.
exact: (@caratheodory_limit_upper R Y (@nonempty_metric_sets R Y)
  (fun j=>val j) (fun j=>metric_real_diameter_cost c p (val j)) (@metric_real_power_measure R Y c p)
  (@metric_real_power_measure_specification R Y c p) (v @` B) delta xi hd hxi).
Qed.
