(** Federer (1969), 3.2.35, p. 272:
    the actual positive distance tubes of a
    nonempty bounded source are nonempty, open
    and bounded, without a measurability premise. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric RealMetricBackground
  MetricSetDistanceUP MetricSetDistanceBasic MetricSetDistanceClosure MetricSetDistanceContinuity
  MetricDistanceTube MetricOpenThickening MetricClosedBalls CoveringFamilyUP CoveringFamilyLaws MetricBoundedUnion MetricBoundedClosureLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_distance_tube_nonempty]:
    nonemptiness of the sets to which the
    boundary formula is applied in Steiner's
    induction, Federer 3.2.35, p. 272.
    An original member has actual distance zero. *)
Lemma euclidean_distance_tube_nonempty (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) d (r:R):
  S!=set0 ->is_metric_set_distance S d ->0<r ->[set x|d x<r]!=set0.
Proof.
move=>[a ha] hD hr; exists a; change (is_true (d a<r)).
by rewrite (metric_set_distance_member hD ha).
Qed.

(** Source for [euclidean_distance_tube_open]:
    openness of the original strict distance
    sublevels in Federer 3.2.35, p. 272.
    This follows directly from the proved
    continuity of every actual distance function. *)
Lemma euclidean_distance_tube_open (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) d (r:R):
  is_metric_set_distance S d ->open [set x|d x<r].
Proof.
move=>hD; rewrite (@metric_distance_tube_thickening R _ S d r hD).
exact:metric_open_thickening_open.
Qed.

(** Source for [euclidean_distance_tube_bounded]:
    boundedness of the original tubes in
    Federer 3.2.35, p. 272. Original
    boundedness supplies a finite radius; actual
    distance approximation and the triangle law
    enlarge it by the positive cutoff r.
    No nearest-point or compact-source premise
    is needed for this support. *)
Lemma euclidean_distance_tube_bounded (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) d (r:R):
  S!=set0 ->is_metric_set_distance S d ->metric_set_bounded S ->0<r ->
  metric_set_bounded [set x|d x<r].
Proof.
move=>[a ha] hD hBound hr.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
have [M [hM hRadius]]:=@metric_bounded_distance_bound R [the metricType R of X] S a hBound.
have hSubset:[set x|d x<r] `<=` metric_closed_ball a (M+r).
  move=>x hx.
  have hError:0<r-d x by rewrite subr_gt0.
  have [b [hb hNear]]:=metric_set_distance_approximation hD x hError.
  rewrite addrC subrK in hNear.
  have hTriangle:=metric_triangle a b x.
  have hFirst:=hRadius b hb.
  change (is_true (mdist a x<=M+r)).
  apply:(le_trans hTriangle _); apply:lerD=>//; apply:ltW.
  by rewrite metric_sym.
have hRadiusNonnegative:0<=M+r:=addr_ge0 hM (ltW hr).
exact:(metric_bounded_subset hSubset (@covering_closed_ball_bounded R [the metricType R of X] a (M+r) hRadiusNonnegative)).
Qed.
