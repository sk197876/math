(** Metric boundary fact supporting the last assertion of Federer (1969),
    2.10.30, p. 195. The boundary of a closed ball is contained in its
    distance sphere. This general-topology fact is valid even when sphere
    and boundary differ, so no extra dimension assumption is imposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_closed_ball_boundary_distance]: supporting
    boundary-to-sphere inclusion for Z=Bdry B(0,r)
    in 2.10.30, p. 195. Boundary is
    expressed by closure minus interior, its usual
    general-topology definition. No radius sign or
    properness hypothesis is required. *)
Lemma metric_closed_ball_boundary_distance (R : realType) (X : metricType R)
    (a : X) (r : R) :
  closure (metric_closed_ball a r) `\` interior (metric_closed_ball a r) `<=`
    [set x | mdist a x=r].
Proof.
move=> x [hx hnot].
rewrite -((closure_id _).1 (@metric_closed_ball_closed R X a r)) in hx.
have hxr : mdist a x<=r := hx.
have hrx : r<=mdist a x.
  rewrite leNgt; apply/negP=> hstrict; apply: hnot.
  have hnb : nbhs x [set y | mdist a y<r].
    apply: open_nbhs_nbhs; split; [exact: metric_open_ball_open|exact hstrict].
  have hsub : [set y | mdist a y<r] `<=` metric_closed_ball a r.
    by move=> y hy; exact: ltW hy.
  exact (filterS hsub hnb).
apply/eqP; by rewrite eq_le hxr hrx.
Qed.
