(** Federer (1969), 2.2.9, p. 65: the target metric space has no isolated
    points. We retain that topological definition and derive the punctured-
    ball formulation needed for the disjoint open-set construction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [has_no_isolated_points]: Federer 2.2.9, p. 65, the stated
    topological hypothesis: no point has an open singleton. *)
Definition has_no_isolated_points (T : topologicalType) : Prop :=
  forall x : T, ~ open [set x].

(** Source for [nonisolated_metric_point_near]: supporting metric
    formulation of Federer 2.2.9, p. 65: every positive-radius ball about a
    point contains a different point. *)
Lemma nonisolated_metric_point_near (R : realType) (T : metricType R) :
  has_no_isolated_points T -> forall (x : T) (r : R), 0 < r ->
  exists y, (0 < mdist x y) /\ mdist x y < r.
Proof.
move=> hT x r hr; case: (pselect (exists y, (0 < mdist x y) /\ mdist x y < r))=> h; first exact h.
exfalso; apply: (hT x).
have he : [set y | mdist x y < r] = [set x].
  apply/seteqP; split.
  - move=> y hy; case: (eqVneq x y)=> [->|hxy]; first by [].
    exfalso; apply: h; exists y; split=> //; by rewrite mdist_gt0.
  - move=> y ->; by rewrite /= mdistxx.
rewrite -he; exact: metric_open_ball_open.
Qed.

(** Source for [punctured_balls_no_isolated_points]: supporting converse for
    Federer 2.2.9, p. 65: nonempty punctured balls rule out open singletons. *)
Lemma punctured_balls_no_isolated_points (R : realType) (T : metricType R) :
  (forall (x : T) (r : R), 0 < r -> exists y, (0 < mdist x y) /\ mdist x y < r) ->
  has_no_isolated_points T.
Proof.
move=> h x ho; rewrite openE in ho.
have hn : nbhs x [set x] := ho x (erefl _).
have [r hr hb] := proj1 (metricType_numDomainType.nbhs_mdistP x [set x]) hn.
have [y [hxy hy]] := h x r hr.
have he := hb y hy; by move: hxy; rewrite he mdistxx ltxx.
Qed.
