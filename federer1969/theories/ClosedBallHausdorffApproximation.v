(** Local counterexample completing the review of the
    closed-ball proof remark in Federer (1969),
    2.10.24, p. 188. See
    ClosedBallHausdorffCounterexample.v for the compact
    real subspace and the obstruction to a limiting
    ball. Here actual positive-radius relative closed
    balls approach that non-ball in the sealed
    Hausdorff metric. Distances of the induced subspace
    are unchanged by its inclusion in the real line.
    This concerns the proof remark, not a disproof
    of the spherical integral equality. The erratum
    p. 4, book p. 188 line 21, only corrects
    the script S notation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module lra.
From Federer Require Import RealMetricBackground CompactSetDistanceProfile MetricSetDistanceUP
  HausdorffDistanceUP HausdorffDistanceBasic HausdorffDistance CompactHausdorffMetric
  ClosedBallHausdorffCounterexample.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [split_ball_truncation]: local approximating
    balls for the correction to 2.10.24, p. 188.
    Only the leftmost interval endpoint moves; the
    positive component remains fixed. *)
Definition split_ball_truncation (R : realType) (h : R) : set (real_line_metric R) :=
  `[-1+3*h,-(2:R)^-1] `|` `[(2:R)^-1,1].

(** Source for [split_ball_truncation_compact]: local compactness
    of each approximating ball used in the correction
    to 2.10.24, p. 188. *)
Lemma split_ball_truncation_compact (R : realType) (h : R) : compact (split_ball_truncation h).
Proof. apply: compactU; exact: segment_compact. Qed.

(** Source for [split_ball_truncation_is_ball]: actual relative
    closed balls in the compact real subspace, for
    the local correction to 2.10.24, p. 188.
    Centre 1/2+h and positive radius 3/2-2h exclude
    both isolated outer points. *)
Theorem split_ball_truncation_is_ball (R : realType) (h : R) :
  0<h -> h<=(8:R)^-1 -> is_split_space_positive_closed_ball (split_ball_truncation h).
Proof.
move=> hh hb; exists ((2:R)^-1+h),(3*(2:R)^-1-2*h); split.
- left; left; right; apply/split_ball_interval_bounds; split; lra.
- split; first by lra.
  move=> x; split.
  + move=> [hx|hx]; move/split_ball_interval_bounds: hx=> [hx1 hx2]; split.
    * left; left; left; apply/split_ball_interval_bounds; split; lra.
    * rewrite ler_norml; apply/andP; split; lra.
    * left; left; right; apply/split_ball_interval_bounds; by split.
    * rewrite ler_norml; apply/andP; split; lra.
  + move=> [hspace hdist]; move: hdist; rewrite ler_norml=> /andP[hd1 hd2].
    case: hspace=> [[hx|hx]|hx].
    * case: hx=> hx; move/split_ball_interval_bounds: hx=> [hx1 hx2].
      -- left; apply/split_ball_interval_bounds; split; lra.
      -- right; apply/split_ball_interval_bounds; by split.
    * have heq : x=(-2:R) := hx; rewrite heq in hd1 hd2; lra.
    * have heq : x=(2:R) := hx; rewrite heq in hd1 hd2; lra.
Qed.

(** Source for [split_ball_truncation_subset]: supporting
    inclusion of the approximating balls in the non-ball
    limit for the local correction to 2.10.24, p. 188. *)
Lemma split_ball_truncation_subset (R : realType) (h : R) :
  0<=h -> split_ball_truncation h `<=` @split_ball_core R.
Proof.
move=> hh x [hx|hx]; [left|right]=> //.
move/split_ball_interval_bounds: hx=> [hx1 hx2]; apply/split_ball_interval_bounds; split; lra.
Qed.

(** Source for [split_ball_truncation_hausdorff_bound]: local
    Hausdorff convergence estimate for the correction to
    2.10.24, p. 188. Every core point is within
    3h of the truncated core and the latter is contained
    in the core. The statement uses arbitrary compact
    representatives and only the sealed distance laws. *)
Theorem split_ball_truncation_hausdorff_bound (R : realType) (h : R)
    (C D : compact_metric_set [the metricType R of real_line_metric R]) :
  0<h -> h<=(8:R)^-1 -> val C=@split_ball_core R -> val D=split_ball_truncation h ->
  hausdorff_distance C D<=3*h.
Proof.
move=> hh hb hC hD.
have h3 : 0<=3*h by lra.
apply: (proj2 (hausdorff_distance_directed_bound (@hausdorff_distance_specification R _) C D h3)).
split=> x hx.
- have hxC : @split_ball_core R x by rewrite -hC.
  have [hxD|hxD] := pselect (split_ball_truncation h x).
  + have hxD' : val D x by rewrite hD.
    apply: le_trans (@metric_set_distance_lower R _ (val D) (compact_set_distance_profile D)
      (compact_set_distance_profile_specification D) x x hxD') _.
    by rewrite mdistxx.
  + have hy : val D (-1+3*h).
      rewrite hD; left; apply/split_ball_interval_bounds; split; lra.
    apply: le_trans (@metric_set_distance_lower R _ (val D) (compact_set_distance_profile D)
      (compact_set_distance_profile_specification D) x (-1+3*h) hy) _.
    rewrite real_line_metric_distanceE ler_norml; apply/andP; split.
    * case: hxC=> /split_ball_interval_bounds [hx1 hx2].
      -- have hxsmall : x< -1+3*h.
           rewrite ltNge; apply/negP=> hge; apply: hxD; left; apply/split_ball_interval_bounds; by split.
         lra.
      -- exfalso; apply: hxD; right; apply/split_ball_interval_bounds; by split.
    * case: hxC=> /split_ball_interval_bounds [hx1 hx2].
      -- have hxsmall : x< -1+3*h.
           rewrite ltNge; apply/negP=> hge; apply: hxD; left; apply/split_ball_interval_bounds; by split.
         lra.
      -- exfalso; apply: hxD; right; apply/split_ball_interval_bounds; by split.
- have hxC : val C x.
    rewrite hC.
    have hxD : split_ball_truncation h x by rewrite -hD.
    exact (@split_ball_truncation_subset R h (ltW hh) x hxD).
  apply: le_trans (@metric_set_distance_lower R _ (val C) (compact_set_distance_profile C)
    (compact_set_distance_profile_specification C) x x hxC) _.
  by rewrite mdistxx.
Qed.

(** Source for [closed_ball_hausdorff_closedness_counterexample]:
    local correction to the Hausdorff-closed-ball remark
    in 2.10.24, p. 188. In the compact real
    subspace X, actual positive-radius closed balls
    approach the non-ball C arbitrarily closely.
    The Hausdorff distance is that of the induced
    metric, represented through the isometric inclusion
    of X in the real line. No claim about the
    spherical integral equality is negated by this example. *)
Theorem closed_ball_hausdorff_closedness_counterexample (R : realType) :
  exists C : compact_metric_set [the metricType R of real_line_metric R],
    val C=@split_ball_core R /\ ~ is_split_space_positive_closed_ball (val C) /\
    forall e : R, 0<e ->
      exists D : compact_metric_set [the metricType R of real_line_metric R],
        is_split_space_positive_closed_ball (val D) /\ hausdorff_distance C D<e.
Proof.
have hCne : @split_ball_core R !=set0.
  exists 1; right; apply/split_ball_interval_bounds; split; lra.
pose C : compact_metric_set [the metricType R of real_line_metric R] := exist _ (@split_ball_core R)
  (mem_set (conj (@split_ball_core_compact R) hCne)).
exists C; split=> //; split; first exact: split_ball_core_not_closed_ball.
move=> e he; pose h := Order.min (e / 6) (1 / 16).
have hh : 0<h by rewrite /h lt_min !divr_gt0 // ltr0n.
have hsmall : h<=(8:R)^-1.
  have hm : h<=1 / 16 by rewrite /h ge_min lexx orbT.
  lra.
have herr : 3*h<e.
  have hm : h<=e / 6 by rewrite /h ge_min lexx.
  lra.
have hDne : split_ball_truncation h !=set0.
  exists 1; right; apply/split_ball_interval_bounds; split; lra.
pose D : compact_metric_set [the metricType R of real_line_metric R] := exist _ (split_ball_truncation h)
  (mem_set (conj (@split_ball_truncation_compact R h) hDne)).
exists D; split; first exact: (@split_ball_truncation_is_ball R h hh hsmall).
apply: le_lt_trans _ herr; exact: (@split_ball_truncation_hausdorff_bound R h C D hh hsmall erefl erefl).
Qed.
