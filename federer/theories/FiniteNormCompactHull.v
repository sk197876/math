(** Federer (1969), 2.10.21, p. 184: the convex hull of a nonempty compact
    set remains compact in a finite-dimensional normed vector space.
    Translate a member to zero, use the proved compact subconvex
    combinations, and identify the result by the hull's universal property.
    editions and proof-route comparison: NormSubconvexCompact.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormMetricContinuity TopologicalProductMaps
  InnerConvex ConvexHullUP ConvexHull ConvexFiniteCombinations ConvexTranslatedCombinations
  SubconvexCombinations NormSubconvexCompact LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_translation_continuous]: supporting
    continuity of translation in the compact hull
    argument for 2.10.21, p. 184. *)
Lemma norm_translation_continuous (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (c : V) :
  continuous (fun x : real_norm_metric_space hN => (x+c : real_norm_metric_space hN)).
Proof.
have hid : continuous (fun x : real_norm_metric_space hN => x) by move=> x U hU.
have hp := topological_pair_continuous hid (@cst_continuous (real_norm_metric_space hN)
  (real_norm_metric_space hN) c).
move=> x; exact: continuous_comp (hp x) (@real_norm_metric_add_continuous R V N hN (x,c)).
Qed.

(** Source for [finite_norm_compact_convex_hull]: supporting
    compact-hull fact used in 2.10.21, p. 184,
    for an arbitrary norm and finite basis, including
    dimension zero. No inner product is chosen. *)
Theorem finite_norm_compact_convex_hull (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) d (e : 'I_d -> V)
    (C : set (real_norm_metric_space hN)) :
  is_basis e -> compact C -> C !=set0 -> compact (@convex_hull R V C : set (real_norm_metric_space hN)).
Proof.
move=> he hC [c hc].
pose D : set (real_norm_metric_space hN) := [set x | C (x+c)].
have hD0 : D 0 by rewrite /D /= add0r.
have hDimage : D=(fun x : real_norm_metric_space hN => (x-c : real_norm_metric_space hN)) @` C.
  apply/seteqP; split=> x hx.
  - exists (x+c); first exact hx; by rewrite addrK.
  - have [y hy <-] := hx; by rewrite /D /= subrK.
have hDc : compact D.
  rewrite hDimage; apply: continuous_compact hC; apply: continuous_subspaceT.
  exact: norm_translation_continuous.
pose S : set (real_norm_metric_space hN) := subconvex_combinations D.
have hS := @subconvex_hull_laws R V D hD0.
pose T : set (real_norm_metric_space hN) := (fun x => x+c) @` S.
have hT : @is_convex_hull R V C T.
  constructor.
  - move=> x hx; exists (x-c); last by rewrite subrK.
    apply: (@convex_hull_includes_law R V D S hS); by rewrite /D /= subrK.
  - move=> x y [u hu <-] [v hv <-] t ht ht1.
    exists ((1-t)*:u+t*:v).
    + exact: (@convex_hull_convex_law R V D S hS u v hu hv t ht ht1).
    + by rewrite !scalerDr addrACA -scalerDl subrK scale1r.
  - move=> E hCE hEc x [y hy <-].
    have hDE : D `<=` [set z | E (z+c)] by move=> z hz; exact: hCE _ hz.
    exact: (@convex_hull_least_law R V D S hS [set z | E (z+c)] hDE
      (@convex_translate_to_origin R V E c hEc) y hy).
have hTc : compact T.
  apply: continuous_compact.
  - have ht : continuous (fun x : real_norm_metric_space hN => (x+c : real_norm_metric_space hN)) :=
      @norm_translation_continuous R V N hN c.
    exact: continuous_subspaceT ht.
  - exact: (@norm_subconvex_combinations_compact R V N hN D hDc d e he).
have heq := @convex_hull_unique R V C T (@convex_hull R V C) hT
  (@convex_hull_specification R V C).
by rewrite heq in hTc.
Qed.
