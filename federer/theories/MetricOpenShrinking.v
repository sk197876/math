(** Supporting metric topology for Federer (1969), 2.2.9, p. 65: choose
    small open subsets whose closures remain inside a prescribed open
    parent. Source context: NoIsolatedPoints.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_open_ball_closure_bound]: supporting
    closure estimate for Federer 2.2.9, p. 65: the closure
    of the strict-radius ball is contained in the closed-radius ball.
    Equality is not assumed for an arbitrary metric space. *)
Lemma metric_open_ball_closure_bound (R : realType) (T : metricType R) (x : T) r :
  closure [set y | mdist x y < r] `<=` metric_closed_ball x r.
Proof.
have hsub : [set y | mdist x y < r] `<=` metric_closed_ball x r.
  move=> y hy; exact: ltW hy.
move=> y hy; apply: (@metric_closed_ball_closed R T x r).
exact: (@closureS T [set z | mdist x z < r] (metric_closed_ball x r) hsub y hy).
Qed.

(** Source for [metric_open_contains_closed_ball]: supporting neighborhood
    shrinking for Federer 2.2.9, p. 65: every point in an open set has a
    positive closed-radius ball contained in that set. *)
Lemma metric_open_contains_closed_ball (R : realType) (T : metricType R)
    (U : set T) x : open U -> U x -> exists r : R,
  0 < r /\ metric_closed_ball x r `<=` U.
Proof.
move=> ho hx; rewrite openE in ho.
have [d hd hb] := proj1 (metricType_numDomainType.nbhs_mdistP x U) (ho x hx).
have h2 : (0 < (2 : R))%R by rewrite ltr0n.
have hr : 0 < d/2 by rewrite divr_gt0.
have hrd : d/2 < d.
  by rewrite (ltr_pdivrMr _ _ h2) -{1}[d]mulr1 (ltr_pM2l hd) ltr1n.
exists (d/2); split=> // y hy; apply: hb; exact: le_lt_trans hy hrd.
Qed.

(** Source for [metric_small_open_with_closed_parent]: supporting
    step in Federer 2.2.9, p. 65: around any point of an
    open parent, choose a nonempty open ball with closure in the
    parent and with all closure distances strictly below e. *)
Lemma metric_small_open_with_closed_parent (R : realType) (T : metricType R)
    (U : set T) x e : open U -> U x -> 0 < e -> exists V : set T,
  open V /\ V x /\ closure V `<=` U /\
  forall y z, closure V y -> closure V z -> mdist y z < e.
Proof.
move=> ho hx he; have [r [hr hsub]] := metric_open_contains_closed_ball ho hx.
pose q := Order.min r (e/4).
have he4 : 0 < e/4 by rewrite divr_gt0 // ltr0n.
have hq : 0 < q by rewrite /q lt_min hr he4.
have hqr : q <= r by rewrite /q ge_min lexx.
have hqe : q <= e/4 by rewrite /q ge_min lexx orbT.
exists [set y | mdist x y < q]; split; first exact: metric_open_ball_open.
split; first by rewrite /= mdistxx.
split.
- move=> y hy; apply: hsub.
  exact: le_trans (metric_open_ball_closure_bound hy) hqr.
- move=> y z hy hz.
  have hdy := metric_open_ball_closure_bound hy.
  have hdz := metric_open_ball_closure_bound hz.
  apply: le_lt_trans (metric_closed_ball_diameter_bound hdy hdz) _.
  apply: le_lt_trans (lerD hqe hqe) _.
  have h4 : (0 < (4 : R))%R by rewrite ltr0n.
  have hsum : e/4 + e/4 = e*2/4 by rewrite mulr_natr mulr2n mulrDl.
  by rewrite hsum (ltr_pdivrMr _ _ h4) (ltr_pM2l he) ltr_nat.
Qed.
