(** Federer (1969), 2.10.40, printed pp. 199–200: the feasible-centre sets
    Y_t are closed, compact when the parameter family is nonempty, and
    increase with t for positive radii. These consequences are proved from
    their defining constraints before selecting any minimising centre. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerProductUP
  InnerNorm InnerNormInequalities InnerMetric InnerBoundedness InnerFiniteCompactness
  MetricClosedBalls WeightedBallMinimumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weighted_ball_centres_intersection]: direct
    intersection of the balls B(a,r t) describing
    Y_t in 2.10.40, p. 200. The norm
    difference is symmetric, so the metric and vector
    formulations agree also for negative auxiliary radii. *)
Lemma weighted_ball_centres_intersection (R : realType) n P (t : R) :
  @weighted_ball_centres R n P t=
    \bigcap_(p in P) @metric_closed_ball R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] p.1 (p.2*t).
Proof.
apply/seteqP; split=> y hy p hp.
- change (is_true (inner_norm (@euclidean_inner_productP R n) (p.1-y)<=p.2*t)).
  rewrite -[p.1-y]opprB inner_normN; exact: hy p hp.
- have hh := hy p hp.
  change (is_true (inner_norm (@euclidean_inner_productP R n) (p.1-y)<=p.2*t)) in hh.
  by rewrite -[p.1-y]opprB inner_normN in hh.
Qed.

(** Source for [weighted_ball_centres_closed]: direct
    closedness of Y_t in the compactness argument
    of 2.10.40, p. 200. No compactness or
    positivity of the parameter family is needed here. *)
Lemma weighted_ball_centres_closed (R : realType) n P (t : R) :
  closed (@weighted_ball_centres R n P t).
Proof.
rewrite weighted_ball_centres_intersection.
apply: closed_bigI=> p hp; exact: metric_closed_ball_closed.
Qed.

(** Source for [weighted_ball_centres_compact]: direct
    compactness of Y_t in 2.10.40, p. 200.
    A single prescribed ball bounds it, and the
    Euclidean closed bounded compactness theorem applies.
    Empty feasible sets remain allowed. *)
Lemma weighted_ball_centres_compact (R : realType) n P (t : R) :
  P !=set0 -> compact (@weighted_ball_centres R n P t).
Proof.
move=> [p hp].
apply: (@inner_finite_basis_boundedly_compact R (R_n R n) _ (@euclidean_inner_productP R n)
  n (@coordinate_basis R n) (@coordinate_basisP R n)); first exact: weighted_ball_centres_closed.
exists (inner_norm (@euclidean_inner_productP R n) p.1+p.2*t)=> y hy.
have hball := hy p hp.
have hh := @inner_norm_triangle R (R_n R n) _ (@euclidean_inner_productP R n) (y-p.1) p.1.
rewrite subrK in hh; apply: le_trans hh _; rewrite addrC lerD2l.
exact hball.
Qed.

(** Source for [weighted_ball_centres_monotone]: supporting
    nesting Y_s subset Y_t for s<=t in
    2.10.40, p. 200. This follows from
    positivity of the prescribed radii. *)
Lemma weighted_ball_centres_monotone (R : realType) n P (s t : R) :
  @positive_ball_parameter_family R n P -> s<=t ->
  weighted_ball_centres P s `<=` weighted_ball_centres P t.
Proof.
move=> hP hst y hy p hp.
exact: le_trans (hy p hp) (ler_wpM2l (ltW (hP p hp)) hst).
Qed.
