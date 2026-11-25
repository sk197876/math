(** Federer (1969), 2.6.6, pp. 120–121: supporting uniform density of
    finite-coordinate and inverse-limit pullbacks. This proves the lattice
    form of the compact approximation argument described in Kelley, General
    Topology, Dover 2017 reprint of 1955, Chapter 7 Problem R(a)(ii)–(iii),
    pp. 244–245. The first cover gives an approximant touching at one point
    and bounded below everywhere; a second cover gives uniform
    approximation. The min/max order is the dual of Kelley's printed order. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology lra.
From Federer Require Import RealMetricBackground CompactFiniteCover FunctionLatticeUP
  FiniteFunctionLatticeExtrema ContinuousEqualNeighborhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_lattice_one_point_approximation]: supporting
    one-point approximation in Kelley 7.R(a)(iii), p. 244,
    for the density assertion of Federer 2.6.6, pp. 120–121.
    It is stated for a lattice, so no algebraic approximation of
    absolute value is needed. *)
Theorem compact_lattice_one_point_approximation (R : realType) (X : topologicalType)
    (L : set (X -> R)) (f : X -> R) (x : X) (e : R) :
  compact (@setT X) -> is_function_lattice L ->
  (forall g, L g -> continuous (g : X -> real_line_metric R)) ->
  continuous (f : X -> real_line_metric R) -> 0<e ->
  (forall y, exists g, L g /\ g x=f x /\ g y=f y) ->
  exists g, L g /\ g x=f x /\ forall z, f z-e<g z.
Proof.
move=> hc hL hcts hf he hinter.
pose G y := sval (cid (hinter y)).
have hG y := svalP (cid (hinter y)).
pose V y := interior [set z | `|G y z-f z|<e].
have hV y : open (V y) := open_interior _.
have hVy y : V y y.
  exact: continuous_equal_uniform_neighborhood (hcts _ (hG y).1) hf (hG y).2.2 he.
have hcover : [set: X] `<=` \bigcup_(y in setT) V y.
  move=> y _; exists y=> //; exact: hVy.
have [D hD hcov] := @compact_open_finite_cover X X setT V setT hc (fun y _=>hV y) hcover.
pose s := [seq G y | y <- D].
pose g := function_maximum_list (G x) s.
have hs : forall u, u \in s -> L u.
  by move=> u /mapP[y hy ->]; exact: (hG y).1.
exists g; split.
- exact (@function_maximum_list_membership R X L hL (G x) s (hG x).1 hs).
split.
- apply: function_maximum_list_common_value; first exact: (hG x).2.1.
  by move=> u /mapP[y hy ->]; exact: (hG y).2.1.
- move=> z; have [y hy hz] := hcov z Logic.I.
  have herr : `|G y z-f z|<e := interior_subset hz.
  have hlo : f z-e<G y z.
    move: herr; rewrite ltr_norml=> /andP[h1 h2]; lra.
  apply: lt_le_trans hlo _; apply: function_maximum_list_member_bound.
  by apply/mapP; exists y.
Qed.

(** Source for [compact_lattice_two_point_density]: the lattice
    form of the Stone–Weierstrass density argument in Kelley
    7.R(a), pp. 244–245, supporting the inverse-limit extension
    in Federer 2.6.6, pp. 120–121. Two-point interpolation is
    an explicit premise, to be proved for the projection pullbacks. *)
Theorem compact_lattice_two_point_density (R : realType) (X : topologicalType)
    (L : set (X -> R)) (x0 : X) (f : X -> R) (e : R) :
  compact (@setT X) -> is_function_lattice L ->
  (forall g, L g -> continuous (g : X -> real_line_metric R)) ->
  continuous (f : X -> real_line_metric R) -> 0<e ->
  (forall x y, exists g, L g /\ g x=f x /\ g y=f y) ->
  exists g, L g /\ forall x, `|f x-g x|<e.
Proof.
move=> hc hL hcts hf he hinter.
have hstep x := @compact_lattice_one_point_approximation R X L f x e hc hL hcts hf he (hinter x).
pose H x := sval (cid (hstep x)).
have hH x := svalP (cid (hstep x)).
pose V x := interior [set z | `|H x z-f z|<e].
have hV x : open (V x) := open_interior _.
have hVx x : V x x.
  exact: continuous_equal_uniform_neighborhood (hcts _ (hH x).1) hf (hH x).2.1 he.
have hcover : [set: X] `<=` \bigcup_(x in setT) V x.
  move=> x _; exists x=> //; exact: hVx.
have [D hD hcov] := @compact_open_finite_cover X X setT V setT hc (fun x _=>hV x) hcover.
pose s := [seq H x | x <- D].
pose g := function_minimum_list (H x0) s.
have hs : forall u, u \in s -> L u.
  by move=> u /mapP[x hx ->]; exact: (hH x).1.
exists g; split; first exact (@function_minimum_list_membership R X L hL (H x0) s (hH x0).1 hs).
move=> z.
have hlo : f z-e<g z.
  apply: function_minimum_list_strict_lower; first exact: (hH x0).2.2.
  by move=> u /mapP[x hx ->]; exact: (hH x).2.2.
have [x hx hz] := hcov z Logic.I.
have herr : `|H x z-f z|<e := interior_subset hz.
have hupper : H x z<f z+e.
  move: herr; rewrite ltr_norml=> /andP[h1 h2]; lra.
have hmin : g z<=H x z.
  apply: function_minimum_list_member_bound; by apply/mapP; exists x.
have hhi := le_lt_trans hmin hupper.
rewrite ltr_norml; apply/andP; split; lra.
Qed.
