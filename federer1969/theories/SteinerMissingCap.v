(** Moving a missing spherical cap in Federer (1969), 2.10.31, p. 196. Use
    exactly the printed chord normal and the sphere exclusion from 2.10.30.
    Equal cap centres require no symmetrisation, avoiding division by a zero
    chord. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import InnerProductUP InnerNorm InnerMetric InnerNormalization
  CompactSetDistanceProfile CompactHausdorffMetric MetricClosedBalls UnitNormalGeometry
  NormalReflectionBoundary SteinerChordReflection SteinerStableFamilyUP
  SteinerSymmetrisationUP SteinerSphereBoundary SteinerBallBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [steiner_move_missing_cap]: supporting
    induction step T_(j-1) to T_j in 2.10.31,
    p. 196. Old missing sphere points remain absent;
    reflection moves the initial missing cap to the
    prescribed sphere centre y. *)
Theorem steiner_move_missing_cap (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (C : set (compact_hausdorff_space (inner_metric_space hB)))
    (S : compact_hausdorff_space (inner_metric_space hB))
    (a y : inner_metric_space hB) (r e : R) :
  is_steiner_stable_family hB C -> C S -> 0<=r ->
  (forall x, val S x -> inner_norm hB x<=r) ->
  inner_norm hB a=r -> inner_norm hB y=r ->
  (forall x, inner_norm hB x=r -> metric_closed_ball a e x -> ~val S x) ->
  exists T : compact_hausdorff_space (inner_metric_space hB),
    C T /\ (forall x, val T x -> inner_norm hB x<=r) /\
    (forall x, inner_norm hB x=r -> ~val S x -> ~val T x) /\
    (forall x, inner_norm hB x=r -> metric_closed_ball y e x -> ~val T x).
Proof.
move=> hC hS hr hb ha hy hmiss.
case: (eqVneq a y)=> [hay|hay].
- exists S; split=> //; split=> //; split=> // x hx hball.
  by apply: hmiss hx _; rewrite hay.
- pose u := inner_normalize hB (y-a).
  have [hu hmove] := @unit_chord_reflection R V B hB a y hay (eq_trans ha (esym hy)).
  have [T [hT hs]] := hC S hS u hu.
  have hbound := steiner_preserves_centered_ball hs hr hb.
  exists T; split=> //; split=> //; split.
  + move=> x hx hn hxT; apply: hn.
    exact (steiner_sphere_endpoints hs (set_valP S).1 hr hb hxT hx).1.
  + move=> x hx hball hxT.
    have hp := (steiner_sphere_endpoints hs (set_valP S).1 hr hb hxT hx).2.
    have hxr : inner_norm hB (normal_reflection hB u x)=r.
      by rewrite (@normal_reflection_norm R V B hB u hu x).
    have hcap : metric_closed_ball a e (normal_reflection hB u x).
      change (is_true (mdist a (normal_reflection hB u x : inner_metric_space hB)<=e)).
      rewrite -{1}(@normal_reflectionK R V B hB u hu a)
        (@normal_reflection_distance R V B hB u hu (normal_reflection hB u a) x) hmove.
      exact hball.
    exact: hmiss _ hxr hcap hp.
Qed.
