(** Federer (1969), 2.10.7, p. 174: the final interval construction equals
    each positive-cutoff approximation and assigns a bounded open interval
    at most its printed increment cost. The positive measure induced by g
    lies below this construction by its already proved interval bound and
    the countable-cover inequality. Source context and the raw/one-sided
    cost distinction: StieltjesScaleSubdivision.v and
    StieltjesInducedOpenIntervals.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground StieltjesCaratheodoryUP StieltjesCaratheodory
  StieltjesIntervalBounds StieltjesScalePointNull StieltjesScaleSubdivision
  StieltjesInducedOpenIntervals StieltjesImageMeasures StieltjesInducedPairLaws StieltjesMonotone
  MetricScaleMeasureBound CaratheodoryLimitUP MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [stieltjes_caratheodory_all_scales]: direct
    equality of the selected final construction
    with all positive size approximations in
    Federer 2.10.7, p. 174, including infinity. *)
Theorem stieltjes_caratheodory_all_scales (R : realType) (g : R -> R) (delta : \bar R) :
  (forall x y, (x<=y)%R -> (g x<=g y)%R) -> 0<delta ->
  forall A, stieltjes_caratheodory_measure g A=stieltjes_caratheodory_scale g delta A.
Proof.
move=> hg hd; exact: (@stieltjes_limit_equals_every_scale R g
  (stieltjes_caratheodory_measure g) (stieltjes_caratheodory_scale g delta) delta hg
  (stieltjes_caratheodory_specification g) hd (stieltjes_caratheodory_scale_specification g delta)).
Qed.

(** Source for [stieltjes_caratheodory_interval_bound]:
    direct upper interval bound in the proof
    of Federer 2.10.7, p. 174. Original
    interval endpoints may be discontinuities. *)
Lemma stieltjes_caratheodory_interval_bound (R : realType) (g : R -> R) (a b : R) :
  (forall x y, (x<=y)%R -> (g x<=g y)%R) -> (a<b)%R ->
  stieltjes_caratheodory_measure g `]a,b[<=(g b-g a)%:E.
Proof.
move=> hg hab; rewrite (@stieltjes_caratheodory_all_scales R g 1 hg lte01 `]a,b[).
exact: (@stieltjes_scale_all_interval_bound R g 1 (stieltjes_caratheodory_scale g 1)
  hg (stieltjes_caratheodory_scale_specification g 1) lte01 a b hab).
Qed.

(** Source for [stieltjes_caratheodory_continuity_point_null]:
    supporting zero atom at each continuity
    point in Federer 2.10.7, p. 174,
    now for the actual final construction. *)
Lemma stieltjes_caratheodory_continuity_point_null (R : realType) (g : R -> R) (x : R) :
  (forall a b, (a<=b)%R -> (g a<=g b)%R) -> g @ x --> g x ->
  stieltjes_caratheodory_measure g [set x]=0.
Proof.
move=> hg hc; rewrite (@stieltjes_caratheodory_all_scales R g 1 hg lte01 [set x]).
exact: (@stieltjes_scale_continuity_point_null R g 1 (stieltjes_caratheodory_scale g 1) x
  hg (stieltjes_caratheodory_scale_specification g 1) lte01 hc).
Qed.

(** Source for [induced_stieltjes_below_caratheodory]:
    supporting reverse interval comparison in
    Federer 2.10.7, pp. 174–175. The existing
    induced measure and its covering law supply
    the lower bound without assuming the desired
    identity between the independent constructions. *)
Theorem induced_stieltjes_below_caratheodory (R : realType) (g : R -> R)
    (mu nu : set R -> \bar R) :
  (forall x y, (x<=y)%R -> (g x<=g y)%R) -> is_induced_measure_pair g mu nu ->
  forall A, mu A<=stieltjes_caratheodory_measure g A.
Proof.
move=> hg hp A.
have hfin := @monotone_locally_finite_variation R g hg.
have [hm _] := @induced_measure_pair_laws R g hfin mu nu hp.
rewrite (@stieltjes_caratheodory_all_scales R g 1 hg lte01 A).
apply: (@measure_bounded_by_metric_scale_envelope R [the metricType R of real_line_metric R]
  (stieltjes_open_intervals R) (@stieltjes_interval_set R) (stieltjes_interval_cost g)
  1 (stieltjes_caratheodory_scale g 1) mu (stieltjes_caratheodory_scale_specification g 1) hm)=> j _.
exact: (@monotone_induced_open_interval_bound R g mu nu (val j).1 (val j).2 hg hp (set_valP j)).
Qed.
