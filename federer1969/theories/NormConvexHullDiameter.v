(** Federer (1969), 2.10.2(1), p. 171, paraphrase: any set and its convex
    hull have equal diameters in a normed vector space. Prove the pairwise
    bound twice by convexity of norm balls, using only the hull's universal
    property and the given norm laws. Arbitrary dimension, empty sets and
    infinite diameter are retained. no identical convex-hull lemma is
    attributed to it. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric InnerConvex ConvexHull
  MetricDiameterUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_ball_inner_convex]: supporting convexity
    of norm balls for Federer 2.10.2(1), p. 171,
    derived directly from homogeneity and the triangle inequality. *)
Lemma norm_ball_inner_convex (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (a : V) (r : R) :
  is_inner_convex [set x | N (x-a)<=r].
Proof.
move=> x y hx hy t ht ht1.
have h1t : 0<=1-t by rewrite subr_ge0.
have he : (1-t) *: (x-a)+t *: (y-a)=(1-t) *: x+t *: y-a.
  by rewrite !scalerBr addrACA -opprD -scalerDl subrK scale1r.
have hh := real_seminorm_triangle hN.1 ((1-t) *: (x-a)) (t *: (y-a)).
rewrite he !(real_seminorm_scale hN.1) (ger0_norm h1t) (ger0_norm ht) in hh.
apply: le_trans hh _.
have hb := lerD (ler_wpM2l h1t hx) (ler_wpM2l ht hy).
by rewrite -mulrDl subrK mul1r in hb.
Qed.

(** Source for [convex_hull_preserves_pair_bound]: supporting
    two applications of convexity in Federer 2.10.2(1),
    p. 171: every finite real pairwise distance bound on A
    also bounds its convex hull. *)
Lemma convex_hull_preserves_pair_bound (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (A : set V) (r : R) :
  (forall x y, A x -> A y -> N (x-y)<=r) ->
  forall x y, convex_hull A x -> convex_hull A y -> N (x-y)<=r.
Proof.
move=> hA x y hx hy.
have hfirst a : A a -> forall z, convex_hull A z -> N (z-a)<=r.
  move=> ha z hz.
  have hAD : A `<=` [set w | N (w-a)<=r] by move=> w hw; exact: hA w a hw ha.
  exact (@convex_hull_least R V A _ hAD (@norm_ball_inner_convex R V N hN a r) z hz).
have hAx : A `<=` [set a | N (a-x)<=r].
  move=> a ha; change (N (a-x)<=r); rewrite (real_seminorm_subtract hN.1 a x).
  exact: hfirst a ha x hx.
have hb := @convex_hull_least R V A _ hAx (@norm_ball_inner_convex R V N hN x r) y hy.
rewrite (real_seminorm_subtract hN.1 x y); exact hb.
Qed.

(** Source for [extended_metric_diameter_convex_hull]: direct
    diameter identity in Federer 2.10.2(1), p. 171,
    for an arbitrary real normed vector space. No closure,
    finite-dimensional or inner-product premise is added. *)
Theorem extended_metric_diameter_convex_hull (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (A : set (real_norm_metric_space hN)) :
  @extended_metric_diameter R (real_norm_metric_space hN) (@convex_hull R V A)=extended_metric_diameter A.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  exact (@extended_metric_diameter_mono R (real_norm_metric_space hN) A (@convex_hull R V A)
    (@convex_hull_includes R V A)).
have hA := extended_metric_diameter_specification A.
apply: (metric_diameter_least (@extended_metric_diameter_specification R (real_norm_metric_space hN) (@convex_hull R V A))
  (metric_diameter_nonnegative hA))=> x y hx hy.
case he: (extended_metric_diameter A) hA=> [r| |] hA.
- rewrite lee_fin real_norm_metric_distanceE.
  apply: (@convex_hull_preserves_pair_bound R V N hN A r _ x y hx hy).
  move=> a b ha hb; have hh := metric_diameter_upper hA ha hb.
  by move: hh; rewrite lee_fin real_norm_metric_distanceE.
- exact: leey.
- by have := metric_diameter_nonnegative hA.
Qed.
