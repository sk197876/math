(** Federer (1969), 2.9.18(1), p. 163: exact scalar ball-ratio values
    throughout the printed radius interval and at its two endpoints. The
    finite arithmetic supports the upper-limit sharpness example. The
    erratum issue in the numerator formula is treated in
    WeightedHitMeasure.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground MetricClosedBalls LebesgueScalarMeasure ScalarLebesgueBallContext
  SparseBallCoverSequenceUP SparseBallCoverRadii SparseWeightedBallValues WeightedHitMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_coefficient_ball_ratio_cancel]: supporting
    finite scalar cancellation in the two endpoint ratios of
    Federer 2.9.18(1), p. 163. A nonzero
    coefficient cancels from c/(a c), leaving the inverse
    of a. Positivity is stronger than needed for this
    arithmetic lemma; actual ball denominators are positive. *)
Lemma positive_coefficient_ball_ratio_cancel (R : realType) (c a : R) :
  (0<c)%R -> (c/(a*c)=a^-1)%R.
Proof.
move=> hc; have hc0 : c!=0%R by rewrite (gt_eqF hc).
by rewrite invfM mulrCA mulfV // mulr1.
Qed.

(** Source for [sparse_scalar_ball_ratio_value]: direct displayed
    ratio formula in Federer 2.9.18(1), p. 163,
    for the whole interval c_(n+1)<=r<=(n+1)c_(n+1).
    The numerator is the exact weighted-hit value and the
    denominator is the actual scalar ball length 2r>0. *)
Theorem sparse_scalar_ball_ratio_value (R : realType)
    (T : set (real_line_metric R)) (c : nat -> R)
    (S : nat -> set (real_line_metric R)) (x : real_line_metric R) (n : nat) (r : R) :
  is_sparse_ball_cover_sequence T c S -> T x ->
  (c n.+1<=r<=((n.+1)%:R*c n.+1))%R ->
  weighted_hit_measure c S (metric_closed_ball x r)/lebesgue_scalar_measure (metric_closed_ball x r)=
    ((c n.+1/(2*r))%R)%:E.
Proof.
move=> h hx /andP [hcr hrb].
have hr : (0<r)%R := lt_le_trans (sparse_cover_radius_positive h n.+1) hcr.
have h2r : (0<2*r)%R by rewrite mulr_gt0 // ltr0n.
have hnum := @sparse_weighted_hit_ball_value R [the metricType R of real_line_metric R]
  T c S x n r h hx (ltac:(by apply/andP; split)).
by rewrite hnum (@scalar_lebesgue_closed_ball R x r (ltW hr)) inver (gt_eqF h2r) -EFinM.
Qed.

(** Source for [sparse_scalar_high_radius_ratio]: direct constant
    ratio 1/2 at r=c_(n+1) in Federer 2.9.18(1),
    p. 163. These arbitrarily small radii force
    the upper limit to be at least 1/2 at every target point. *)
Lemma sparse_scalar_high_radius_ratio (R : realType)
    (T : set (real_line_metric R)) (c : nat -> R)
    (S : nat -> set (real_line_metric R)) (x : real_line_metric R) (n : nat) :
  is_sparse_ball_cover_sequence T c S -> T x ->
  weighted_hit_measure c S (metric_closed_ball x (c n.+1))/
    lebesgue_scalar_measure (metric_closed_ball x (c n.+1))=((1/2)%R : R)%:E.
Proof.
move=> h hx.
have hn : (1<=((n.+1)%:R : R))%R by rewrite ler1n.
have hmul := ler_wpM2r (ltW (sparse_cover_radius_positive h n.+1)) hn.
rewrite mul1r in hmul.
rewrite (@sparse_scalar_ball_ratio_value R T c S x n (c n.+1) h hx
  (ltac:(by apply/andP; split))).
rewrite (positive_coefficient_ball_ratio_cancel 2%R (sparse_cover_radius_positive h n.+1)).
by rewrite mul1r.
Qed.

(** Source for [sparse_scalar_low_radius_ratio]: direct small
    ratio 1/(2(n+1)) at r=(n+1)c_(n+1) in
    Federer 2.9.18(1), p. 163. The lower
    endpoint ratios tend to zero while the preceding constant
    ratios remain 1/2. *)
Lemma sparse_scalar_low_radius_ratio (R : realType)
    (T : set (real_line_metric R)) (c : nat -> R)
    (S : nat -> set (real_line_metric R)) (x : real_line_metric R) (n : nat) :
  is_sparse_ball_cover_sequence T c S -> T x ->
  weighted_hit_measure c S (metric_closed_ball x ((n.+1)%:R*c n.+1)%R)/
    lebesgue_scalar_measure (metric_closed_ball x ((n.+1)%:R*c n.+1)%R)=
    (((2*(n.+1)%:R)%R)^-1)%:E.
Proof.
move=> h hx.
have hn : (1<=((n.+1)%:R : R))%R by rewrite ler1n.
have hmul := ler_wpM2r (ltW (sparse_cover_radius_positive h n.+1)) hn.
rewrite mul1r in hmul.
rewrite (@sparse_scalar_ball_ratio_value R T c S x n ((n.+1)%:R*c n.+1)%R h hx
  (ltac:(by apply/andP; split))) mulrA.
by rewrite (positive_coefficient_ball_ratio_cancel (2*(n.+1)%:R)%R
  (sparse_cover_radius_positive h n.+1)).
Qed.
