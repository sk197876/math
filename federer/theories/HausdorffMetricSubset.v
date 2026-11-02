(** Federer (1969), 2.10.26, pp. 189–190: supporting restriction to compact
    image codomains in the null-fibre reduction. Hausdorff mass of a subset
    is independent of whether it is measured in the ambient space or its
    induced metric space. Derive this from covering-infimum laws of 2.10.1,
    p. 170, and the diameter gauge of 2.10.2, p. 171. No construction is
    unfolded. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import MetricSubsetBackground MetricDiameterUP MetricDiameter HausdorffLengthUP
  HausdorffMeasureUP HausdorffMeasure HausdorffDiameterCost HausdorffPowerCostLaws HausdorffLipschitzImages
  LipschitzUP MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleCutoffCost MetricScaleMeasureBound
  CaratheodoryLimitUP MeasureUP MeasureBasic MeasurePushforward NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_subset_preimage_diameter_bound]: supporting
    subspace cover comparison for 2.10.26, p. 190.
    Restricting a set to the induced metric space
    cannot increase its diameter. The empty preimage
    is covered by the nonnegative diameter convention. *)
Lemma metric_subset_preimage_diameter_bound (R : realType) (Y : metricType R)
    (K A : set Y) :
  extended_metric_diameter ((fun x : metric_subset K=>(val x : Y)) @^-1` A)<=
    extended_metric_diameter A.
Proof.
apply: (metric_diameter_least (extended_metric_diameter_specification _)); first exact: metric_diameter_nonnegative
  (extended_metric_diameter_specification A).
move=> x z hx hz; rewrite metric_subset_distanceE.
exact: (@metric_diameter_upper R Y A _ (extended_metric_diameter_specification A)
  (val x) (val z) hx hz).
Qed.

(** Source for [hausdorff_metric_subset_measure]: supporting
    ambient/subspace equality used in the compact-image
    reduction of 2.10.26, pp. 189–190. The
    actual opaque integer-degree Hausdorff measures occur
    on both sides, including infinite masses and
    arbitrary nonmeasurable subsets. *)
Theorem hausdorff_metric_subset_measure (R : realType) (Y : metricType R)
    (K : set Y) (k : nat) (B : set (metric_subset K)) :
  @hausdorff_measure R Y k ((fun x : metric_subset K=>(val x : Y)) @` B)=
    @hausdorff_measure R [the metricType R of metric_subset K] k B.
Proof.
pose X := [the metricType R of metric_subset K].
pose v := fun x : X=>(val x : Y).
have hv : is_metric_lipschitz_bound setT v 1%R.
  split; first exact: ler01.
  by move=> x z _ _; rewrite metric_subset_distanceE mul1r.
have hupper := @hausdorff_lipschitz_image_bound R X Y v 1%R k hv B.
rewrite expr1n mul1e in hupper.
apply/eqP; rewrite eq_le hupper /=.
apply: (caratheodory_limit_least (@hausdorff_measure_specification R X k))=> delta nu hd hn.
have hnu := metric_scale_envelope_is_measure hn
  (fun j=>hausdorff_diameter_cost_nonnegative k (val j)).
pose xi := @metric_scale_envelope R Y (@nonempty_metric_sets R Y) (fun j=>val j)
  (fun j=>hausdorff_diameter_cost k (val j)) delta.
have hxi := @metric_scale_envelope_specification R Y (@nonempty_metric_sets R Y)
  (fun j=>val j) (fun j=>hausdorff_diameter_cost k (val j)) delta.
have hgen (j : @nonempty_metric_sets R Y) : extended_metric_diameter (val j)<=delta ->
    measure_pushforward v nu (val j)<=hausdorff_diameter_cost k (val j).
  move=> hj; rewrite /measure_pushforward.
  pose C := v @^-1` val j.
  change (is_true (nu C<=hausdorff_diameter_cost k (val j))).
  have hdiam : extended_metric_diameter C<=extended_metric_diameter (val j).
    exact: metric_subset_preimage_diameter_bound.
  case: (pselect (C!=set0))=> [hC|hC].
  - pose i : @nonempty_metric_sets R X := Sub C (mem_set hC).
    have hsize (s : @nonempty_metric_sets R X) (hs : [set i] s) : extended_metric_diameter (val s)<=delta.
      rewrite (hs : s = i); exact: le_trans hdiam hj.
    have hc : C `<=` \bigcup_(s in [set i]) val s by move=> x hx; exists i.
    have hh := @metric_scale_envelope_lower R X (@nonempty_metric_sets R X)
      (fun s=>val s) (fun s=>hausdorff_diameter_cost k (val s)) delta nu hn C [set i]
      (countable1 i) hsize hc.
    rewrite nonnegative_sum_singleton in hh; last exact: hausdorff_diameter_cost_nonnegative.
    apply: le_trans hh _; rewrite /hausdorff_diameter_cost.
    exact: hausdorff_power_cost_monotone (metric_diameter_nonnegative
      (extended_metric_diameter_specification C)) hdiam.
  - have he : C=set0.
      apply/seteqP; split=> [x hx|x []]; exfalso; apply: hC; by exists x.
    rewrite he (measure_empty hnu); exact: hausdorff_diameter_cost_nonnegative.
have hh := @measure_bounded_by_metric_scale_envelope R Y (@nonempty_metric_sets R Y)
  (fun j=>val j) (fun j=>hausdorff_diameter_cost k (val j)) delta xi (measure_pushforward v nu)
  hxi (measure_pushforward_is_measure v hnu) hgen (v @` B).
have he : v @^-1` (v @` B)=B.
  apply/seteqP; split=> [x [z hz heq]|x hx]; last by exists x.
  have ezx : z=x := val_inj heq; by rewrite -ezx.
rewrite /measure_pushforward he in hh.
apply: le_trans hh _.
exact: (@caratheodory_limit_upper R Y (@nonempty_metric_sets R Y)
  (fun j=>val j) (fun j=>hausdorff_diameter_cost k (val j)) (@hausdorff_measure R Y k)
  (@hausdorff_measure_specification R Y k) (v @` B) delta xi hd hxi).
Qed.

(** Source for [hausdorff_metric_subset_preimage]: supporting
    set restriction form of ambient/subspace equality
    for 2.10.26, p. 190. Subsets and fibres
    may be nonmeasurable; this is an equality of
    outer measures, not a measurability transfer assumption. *)
Corollary hausdorff_metric_subset_preimage (R : realType) (Y : metricType R)
    (K A : set Y) k :
  @hausdorff_measure R [the metricType R of metric_subset K] k
    ((fun x : metric_subset K=>(val x : Y)) @^-1` A)=@hausdorff_measure R Y k (K `&` A).
Proof.
rewrite -hausdorff_metric_subset_measure.
congr (hausdorff_measure k _); apply/seteqP; split.
- move=> y [x hx <-]; split=> //; exact: set_valP x.
- move=> y [hyK hyA]; exists (Sub y (mem_set hyK) : metric_subset K); by [].
Qed.
