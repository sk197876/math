(** Federer (1969), 3.2.46, p. 282: localization
    of coordinate maps can be followed by a retraction
    onto a closed Euclidean ball inside the target chart.
    This supporting existence theorem uses the nearest-point
    laws of 1.7.13, p. 37. The auxiliary map remains
    existential; no new globally selected object is exposed. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  InnerNearestUP InnerClosedBallConvex EuclideanClosedBallCompact CompactNearest
  InnerNearestContraction MetricClosedBalls LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_closed_ball_retraction_exists]:
    there is an actual nonexpanding retraction of R^n onto
    every nonnegative-radius closed ball, supporting the
    localization in 3.2.46, p. 282. Its membership,
    fixed-point and Lipschitz laws are all proved from
    actual nearest points, not assumed. Zero radius and
    dimension zero are retained. *)
Theorem euclidean_closed_ball_retraction_exists (R : realType) n
    (a : inner_metric_space (@euclidean_inner_productP R n)) (r : R) :
  0<=r -> exists P : inner_metric_space (@euclidean_inner_productP R n) ->
    inner_metric_space (@euclidean_inner_productP R n),
    (forall x, metric_closed_ball a r (P x)) /\
    (forall x, metric_closed_ball a r x -> P x=x) /\
    is_metric_lipschitz_bound setT P 1.
Proof.
move=> hr.
pose C := metric_closed_ball a r.
pose hE := @euclidean_inner_productP R n.
have hNonempty : C!=set0.
  exists a; change (is_true (mdist a a<=r)); by rewrite mdistxx.
have hCompact := @euclidean_closed_metric_ball_compact R n a r.
have hConvex := @inner_metric_closed_ball_convex R (R_n R n) (@euclidean_inner_product R n) hE a r.
have hExists x : exists p, is_inner_nearest hE x C p.
  exact (@compact_inner_nearest_exists R (R_n R n) (@euclidean_inner_product R n) hE
    x C hNonempty hCompact).
have [P hP] := choice hExists.
exists P; split.
- move=> x; exact: inner_nearest_member_law (hP x).
- split.
  + move=> x hx.
    have hMinimum := inner_nearest_minimal_law (hP x) hx.
    rewrite subrr inner_norm0 in hMinimum.
    have hZero : inner_norm hE (x-P x)=0.
      by apply/eqP; rewrite eq_le hMinimum inner_norm_nonnegative.
    have hFixed : x = P x by move/eqP: hZero; rewrite inner_norm_eq0 subr_eq0=>/eqP.
    exact: esym hFixed.
  + split; first exact: ler01.
    move=> x y _ _; rewrite !inner_metric_distanceE mul1r.
    exact: inner_nearest_pair_nonexpanding hConvex (hP x) (hP y).
Qed.
