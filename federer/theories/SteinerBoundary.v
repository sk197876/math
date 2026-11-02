(** Federer (1969), 2.10.30, p. 195: the final closed-ball boundary
    inclusion, using the actual topological boundary Z. The stronger
    sphere-endpoint theorem and reflection invariance of the boundary
    establish the printed statement. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import InnerProductUP InnerNorm InnerMetric UnitNormalGeometry MetricClosedBalls
  MetricBallBoundary NormalReflectionBoundary SteinerSymmetrisationUP SteinerSphereBoundary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [steiner_closed_ball_boundary_exclusion]: direct
    (Z minus S) union rho_u(Z minus S)
    contained in Z minus T in 2.10.30,
    p. 195, with Z the actual boundary of
    the closed ball. The unit normal ensures
    a genuine perpendicular direction; radius zero
    is included. *)
Theorem steiner_closed_ball_boundary_exclusion (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (u : V) (S T : set (inner_metric_space hB)) (r : R) :
  is_steiner_symmetrisation hB u S T -> compact S -> 0<=r ->
  S `<=` metric_closed_ball (0 : inner_metric_space hB) r ->
  let C := metric_closed_ball (0 : inner_metric_space hB) r in
  let Z := closure C `\` interior C in
  (Z `\` S) `|` (normal_reflection hB u @` (Z `\` S)) `<=` Z `\` T.
Proof.
move=> hT hS hr hbound C Z.
have hu := steiner_unit_normal_law hT.
have hnorm z : S z -> inner_norm hB z<=r.
  move=> hz; move: (hbound z hz).
  by rewrite /metric_closed_ball /= inner_metric_distanceE sub0r inner_normN.
have hzSphere z : Z z -> inner_norm hB z=r.
  move=> hz; have hh := @metric_closed_ball_boundary_distance R (inner_metric_space hB) 0 r z hz.
  change (mdist (0 : inner_metric_space hB) z=r) in hh.
  by move: hh; rewrite inner_metric_distanceE sub0r inner_normN.
move=> x [[hx hxS]|[y [hy hyS] <-]].
- split=> // hxT.
  exact: hxS (steiner_sphere_endpoints hT hS hr hnorm hxT (hzSphere x hx)).1.
- have hx : Z (normal_reflection hB u y).
    exact ((@normal_reflection_ball_boundary R V B hB u hu r y).2 hy).
  split=> // hxT.
  have hh := (steiner_sphere_endpoints hT hS hr hnorm hxT (hzSphere _ hx)).2.
  apply: hyS; by rewrite (@normal_reflectionK R V B hB u hu y) in hh.
Qed.
