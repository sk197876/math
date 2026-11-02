(** Federer (1969), 2.10.21, p. 184: the convex-hull map has Lipschitz
    constant one for the Hausdorff metric. Use convex sublevels of the
    compact convex distance profiles and the universal property of each
    hull. Finite dimension supplies compact hulls, not the distance
    estimate. Neither is claimed to state this Hausdorff estimate. Source
    editions: NormSubconvexCompact.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric InnerConvex ConvexFunctionUP ConvexHullUP ConvexHull
  CompactSetDistanceProfile CompactConvexProfiles MetricSetDistanceUP MetricSetDistanceBasic
  HausdorffDistanceUP HausdorffDistanceBasic HausdorffDistance FiniteNormCompactHull LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_norm_hull_member]: supporting
    membership of a compact convex hull in F,
    2.10.21, p. 184. Dimension zero and
    arbitrary norms are included. *)
Lemma finite_norm_hull_member (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) d (e : 'I_d -> V)
    (C : compact_metric_set (real_norm_metric_space hN)) :
  is_basis e -> compact (@convex_hull R V (val C) : set (real_norm_metric_space hN)) /\
    @convex_hull R V (val C) !=set0.
Proof.
move=> he; split.
- exact: finite_norm_compact_convex_hull he (set_valP C).1 (set_valP C).2.
- have [x hx] := (set_valP C).2; exists x; exact: (@convex_hull_includes R V (val C) x hx).
Qed.

(** Source for [finite_norm_hull]: direct convex-hull
    map on nonempty compact sets in 2.10.21,
    p. 184. Package the already sealed hull
    using its proved compactness, without choosing a
    different hull construction. *)
Definition finite_norm_hull (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) d (e : 'I_d -> V) (he : is_basis e)
    (C : compact_metric_set (real_norm_metric_space hN)) : compact_metric_set (real_norm_metric_space hN) :=
  exist _ (@convex_hull R V (val C)) (mem_set (@finite_norm_hull_member R V N hN d e C he)).

(** Source for [hausdorff_compact_hulls_nonexpanding]: supporting
    one-Lipschitz estimate in 2.10.21, p. 184,
    whenever the two given hulls are compact. The
    estimate itself requires no finite-dimensional hypothesis. *)
Theorem hausdorff_compact_hulls_nonexpanding (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (C D CH DH : compact_metric_set (real_norm_metric_space hN)) :
  val CH=@convex_hull R V (val C) -> val DH=@convex_hull R V (val D) ->
  hausdorff_distance CH DH<=hausdorff_distance C D.
Proof.
move=> hCH hDH.
pose h := hausdorff_distance C D.
have h0 : 0<=h := hausdorff_distance_nonnegative_law (@hausdorff_distance_specification R (real_norm_metric_space hN)) C D.
have hdir := (proj1 (hausdorff_distance_directed_bound
  (@hausdorff_distance_specification R (real_norm_metric_space hN)) C D h0)) (lexx h).
have hside (A B AH BH : compact_metric_set (real_norm_metric_space hN))
    (hAH : val AH=@convex_hull R V (val A)) (hBH : val BH=@convex_hull R V (val B))
    (hAB : forall x, val A x -> compact_set_distance_profile B x<=h) :
    forall x, val AH x -> compact_set_distance_profile BH x<=h.
  have hBc : @is_inner_convex R V (val BH) by rewrite hBH; exact: (@convex_hull_convex R V (val B)).
  have hfun := (proj1 (compact_convex_distance_profile BH) hBc).2.
  pose E : set V := [set x | compact_set_distance_profile BH x<=h].
  have hE : is_inner_convex E.
    move=> x y hx hy t ht ht1.
    have hh := hfun x y I I t ht ht1.
    have h1t : 0<=1-t by rewrite subr_ge0.
    have hb := lerD (ler_wpM2l h1t hx) (ler_wpM2l ht hy).
    rewrite -mulrDl subrK mul1r in hb; exact: le_trans hh hb.
  have hAE : val A `<=` E.
    move=> x hx; apply: le_trans _ (hAB x hx).
    apply: (@metric_set_distance_greatest R (real_norm_metric_space hN) (val B)
      (compact_set_distance_profile B) (compact_set_distance_profile_specification B)
      x (compact_set_distance_profile BH x))=> y hy.
    have hyH : val BH y by rewrite hBH; exact: (@convex_hull_includes R V (val B) y hy).
    exact: (@metric_set_distance_lower R (real_norm_metric_space hN) (val BH)
      (compact_set_distance_profile BH) (compact_set_distance_profile_specification BH) x y hyH).
  move=> x hx; rewrite hAH in hx.
  exact: (@convex_hull_least R V (val A) E hAE hE x hx).
apply: (proj2 (hausdorff_distance_directed_bound
  (@hausdorff_distance_specification R (real_norm_metric_space hN)) CH DH h0)).
split; [exact: hside C D CH DH hCH hDH hdir.1|exact: hside D C DH CH hDH hCH hdir.2].
Qed.

(** Source for [finite_norm_hull_hausdorff_lipschitz]: direct
    one-Lipschitz convex-hull map of 2.10.21,
    p. 184, for an arbitrary finite-dimensional norm. *)
Theorem finite_norm_hull_hausdorff_lipschitz (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) d (e : 'I_d -> V) (he : is_basis e)
    (C D : compact_metric_set (real_norm_metric_space hN)) :
  hausdorff_distance (finite_norm_hull he C) (finite_norm_hull he D)<=hausdorff_distance C D.
Proof.
exact: (@hausdorff_compact_hulls_nonexpanding R V N hN C D
  (@finite_norm_hull R V N hN d e he C) (@finite_norm_hull R V N hN d e he D) erefl erefl).
Qed.
