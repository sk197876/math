(** Minimal-radius sphere argument in Federer (1969), 2.10.31, pp. 195–196.
    Every class member inside a ball of the minimal centred radius contains
    its entire sphere. Follow the finite missing-cap argument. Attainment of
    the radius supplies the final contradiction with the same centre zero,
    correcting the printed centre a in the shrinking-ball inference on p.
    196. This is a local proof correction; Federer's May 1987 erratum has no
    entry for p. 196. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import InnerProductUP InnerNorm InnerMetric CompactSetDistanceProfile
  CompactHausdorffMetric CompactEnclosingRadius MetricClosedBalls LipschitzFunctionCompact
  MetricClosedSeparation SteinerStableFamilyUP SteinerSphereCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [steiner_minimal_radius_contains_sphere]: direct
    assertion Bdry B(0,r) contained in S,
    concluding the cap contradiction in 2.10.31,
    pp. 195–196. We prove it for the whole
    norm sphere, including radius zero. *)
Theorem steiner_minimal_radius_contains_sphere (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (C : set (compact_hausdorff_space (inner_metric_space hB)))
    (S : compact_hausdorff_space (inner_metric_space hB)) (r : R) :
  metric_boundedly_compact (inner_metric_space hB) ->
  is_steiner_stable_family hB C -> C S -> 0<=r ->
  (forall T, C T -> r<=compact_enclosing_radius (0 : inner_metric_space hB) T) ->
  (forall x, val S x -> inner_norm hB x<=r) ->
  forall x : inner_metric_space hB, inner_norm hB x=r -> val S x.
Proof.
move=> hX hC hS hr hmin hb a ha.
case: (pselect (val S a))=> [//|hnot]; exfalso.
have hclosed := compact_closed (@metric_hausdorff R (inner_metric_space hB)) (set_valP S).1.
have [e [he hgap]] := closed_set_missing_closed_ball hclosed hnot.
have hzc : compact [set x : inner_metric_space hB | inner_norm hB x=r].
  have hh := @metric_distance_sphere_compact R (inner_metric_space hB) 0 r hX hr.
  have hE : [set x : inner_metric_space hB | mdist (0 : inner_metric_space hB) x=r]=
      [set x : inner_metric_space hB | inner_norm hB x=r].
    by apply/seteqP; split=> x; rewrite /= inner_metric_distanceE sub0r inner_normN.
  by rewrite hE in hh.
have hmiss (x : inner_metric_space hB) : inner_norm hB x=r -> metric_closed_ball a e x -> ~val S x.
  by move=> _; exact: hgap x.
have [T [hT [hTb hTZ]]] := steiner_remove_missing_sphere hC hS hr he hb hzc ha hmiss.
have hTr : compact_enclosing_radius (0 : inner_metric_space hB) T<=r.
  apply: (compact_enclosing_radius_least (0 : inner_metric_space hB) T hr)=> x hx.
  rewrite /metric_closed_ball /= inner_metric_distanceE sub0r inner_normN; exact: hTb x hx.
have heq : compact_enclosing_radius (0 : inner_metric_space hB) T=r.
  by apply/eqP; rewrite eq_le hTr (hmin T hT).
have [x [hx hrad]] := compact_enclosing_radius_attains (0 : inner_metric_space hB) T.
rewrite inner_metric_distanceE sub0r inner_normN heq in hrad.
exact: hTZ x hrad hx.
Qed.
