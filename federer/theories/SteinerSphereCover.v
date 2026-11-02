(** Finite cap covering argument in Federer (1969), 2.10.31, pp. 195–196.
    Compactness of the sphere gives the finite list of cap centres; the
    preceding iteration then removes the entire sphere. This retains the
    centre zero of the containing ball. The printed shrinking-ball centre a
    on p. 196 is locally corrected separately in
    SteinerRadiusCenterCorrection.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import InnerProductUP InnerNorm InnerMetric CompactSetDistanceProfile
  CompactHausdorffMetric MetricClosedBalls CompactFiniteCover SteinerStableFamilyUP SteinerFiniteCaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [steiner_remove_missing_sphere]: direct
    conclusion Z intersect T_k is empty after
    the cap iteration in 2.10.31, p. 196.
    A single initially missing sphere point suffices,
    with a missing closed neighbourhood of radius e. *)
Theorem steiner_remove_missing_sphere (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (C : set (compact_hausdorff_space (inner_metric_space hB)))
    (S : compact_hausdorff_space (inner_metric_space hB))
    (a : inner_metric_space hB) (r e : R) :
  is_steiner_stable_family hB C -> C S -> 0<=r -> 0<e ->
  (forall x, val S x -> inner_norm hB x<=r) ->
  compact [set x : inner_metric_space hB | inner_norm hB x=r] ->
  inner_norm hB a=r ->
  (forall x, inner_norm hB x=r -> metric_closed_ball a e x -> ~val S x) ->
  exists T : compact_hausdorff_space (inner_metric_space hB),
    C T /\ (forall x, val T x -> inner_norm hB x<=r) /\
    (forall x, inner_norm hB x=r -> ~val T x).
Proof.
move=> hC hS hr he hb hc ha hmiss.
pose Z : set (inner_metric_space hB) := [set x | inner_norm hB x=r].
pose U (y : inner_metric_space hB) := [set x | mdist y x<e].
have hcover : Z `<=` \bigcup_(y in Z) U y.
  move=> x hx; exists x=> //; by rewrite /U /= mdistxx.
have [F hF hcov] := @compact_open_finite_cover (inner_metric_space hB)
  (inner_metric_space hB) Z U Z hc (fun y _=>metric_open_ball_open y e) hcover.
have hs y : y \in enum_fset F -> inner_norm hB y=r.
  move=> hy; have hh := hF y hy; exact (set_mem hh).
have [T [hT [hTb [_ hTs]]]] := steiner_finite_missing_caps hC hS hr hb ha hs hmiss.
exists T; split=> //; split=> // x hx hxT.
have [y hy hxy] := hcov x hx.
exact: (hTs y hy x hx (ltW hxy) hxT).
Qed.
