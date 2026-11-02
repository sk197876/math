(** Federer (1969), 2.10.1, p. 170: pull back uniform open ball covers under
    a continuous map into a metric space. The resulting whole-space open
    covers make refined generators have small image diameter, as required
    for the corrected topological measurability argument through 2.3.2(8),
    p. 74. Source context and corrected cover convention:
    TopologicalCaratheodoryUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals topology.
From Federer Require Import MetricClosedBalls OpenRefiningEnvelopeUP TopologicalCaratheodoryUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_metric_ball_cover]: supporting
    pulled-back uniform ball cover for the corrected topological
    claim of Federer 2.10.1, p. 170. At radius e/2,
    every refined generator has image diameter strictly below e. *)
Definition continuous_metric_ball_cover (R : realType) (X : Type) (Y : metricType R)
    (f : X -> Y) (e : R) := [set U : set X | exists y,
      U=f @^-1` [set z | mdist y z<e/2]].

(** Source for [continuous_metric_ball_cover_whole]: supporting
    open-cover and exhaustion assertions for the corrected
    topological version of Federer 2.10.1, p. 170. *)
Lemma continuous_metric_ball_cover_whole (R : realType) (X : topologicalType)
    (Y : metricType R) (f : X -> Y) (e : R) : continuous f -> 0<e ->
  is_whole_space_open_cover (continuous_metric_ball_cover f e).
Proof.
move=> hf he; split.
- move=> U [y ->]; apply: open_comp; last exact: metric_open_ball_open.
  by move=> x _; exact: hf.
- move=> x _; exists (f @^-1` [set z | mdist (f x) z<e/2]); first by exists (f x).
  by rewrite /= mdistxx divr_gt0 // ltr0n.
Qed.

(** Source for [continuous_ball_cover_generator_image_bound]:
    supporting small-image assertion in the corrected proof
    of Federer 2.10.1, p. 170. Two image points in the
    same strict e/2 ball have distance strictly below e. *)
Lemma continuous_ball_cover_generator_image_bound (R : realType) (X J : Type)
    (Y : metricType R) (S : J -> set X) (f : X -> Y) (e : R) j :
  generator_refines_cover S (continuous_metric_ball_cover f e) j ->
  forall x y, S j x -> S j y -> mdist (f x) (f y)<e.
Proof.
move=> [U [[z ->] hSU]] x y hx hy.
have hx' : mdist z (f x)<e/2 := hSU x hx.
have hy' : mdist z (f y)<e/2 := hSU y hy.
have hhalf : e/2+e/2=e by rewrite -mulr2n -[LHS]mulr_natr divfK ?pnatr_eq0.
have hsum := ltrD hx' hy'; rewrite hhalf in hsum.
apply: le_lt_trans (metric_triangle (f x) z (f y)) _.
by rewrite (metric_sym (f x) z).
Qed.
