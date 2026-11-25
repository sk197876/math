(** Federer (1969), 1.7.13, p. 37: the intersection of C_s, s>0, consists of
    the nearest point. This module separates the diameter-to-zero and
    infimum arguments from completeness. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import InnerProductUP InnerNorm InnerMetric InnerNormedTopology
  InnerSetDistanceUP InnerConvex InnerNearSet InnerNearDiameter InnerNearestUP
  HilbertClosedIntersection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Intersection.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation M := (inner_metric_space hB).
Variable a : M.
Variable C : set M.
Variable d : R.
Hypothesis hd : is_inner_set_distance hB a C d.
Hypothesis hconv : is_inner_convex C.

(** Source for [inner_near_sets_shrink]: Federer 1.7.13,
    p. 37, the diameter bound tends to zero as s tends to zero.
    This is the small-diameter hypothesis of the complete-metric
    intersection theorem. *)
Lemma inner_near_sets_shrink eps : 0 < eps -> exists s, 0 < s /\
  forall x y, inner_near_set hB a C d s x -> inner_near_set hB a C d s y ->
    @inner_distance R V B hB x y < eps.
Proof.
move=> heps.
have h4 : (0 : R) < 4 by rewrite ltr0n.
have hs : 0 < eps/4 by rewrite divr_gt0.
have hlt : 2*(eps/4) < eps.
  by rewrite mulrA (ltr_pdivrMr _ _ h4) [2*eps]mulrC (ltr_pM2l heps) ltr_nat.
exists (eps/4); split=> // x y hx hy.
exact: le_lt_trans (inner_near_diameter hd hconv hs hx hy) hlt.
Qed.

(** Source for [inner_near_intersection_nearest]: Federer
    1.7.13, p. 37, the point in all C_s has distance d
    from a and is therefore a nearest point. *)
Lemma inner_near_intersection_nearest c :
    (forall s, 0 < s -> inner_near_set hB a C d s c) ->
    is_inner_nearest hB a C c.
Proof.
move=> hc.
have hcC := (hc 1 ltr01).1.
have hn2 : inner_norm hB (a-c)^+2 <= d^+2.
  apply/ler_addgt0Pr => eps heps.
  have hs : 0 < Num.sqrt eps by rewrite sqrtr_gt0.
  have hh := (hc _ hs).2.
  rewrite (sqr_sqrtr (ltW heps)) in hh; exact hh.
have hn : inner_norm hB (a-c) <= d.
  by move: hn2; rewrite (ler_sqr (inner_norm_nonnegative hB _) (inner_set_distance_nonnegative_law hd)).
constructor=> // x hx.
exact: le_trans hn (@inner_set_distance_lower_law R V B hB a C d hd x hx).
Qed.

(** Source for [inner_nearest_in_near_sets]: Federer 1.7.13,
    p. 37, every nearest point belongs to every C_s, which
    makes the singleton intersection prove uniqueness. *)
Lemma inner_nearest_in_near_sets c : is_inner_nearest hB a C c ->
  forall s, 0 < s -> inner_near_set hB a C d s c.
Proof.
move=> hc s hs; split; first exact: inner_nearest_member_law hc.
rewrite -(inner_nearest_distance hd hc) lerDl; exact: sqr_ge0.
Qed.

(** Source for [inner_nearest_unique]: Federer 1.7.13,
    p. 37, uniqueness of the nearest point. Convexity suffices
    once nearest points exist; completeness is not needed here. *)
Theorem inner_nearest_unique c e :
    is_inner_nearest hB a C c -> is_inner_nearest hB a C e -> c=e.
Proof.
move=> hc he.
exact (@inner_shrinking_intersection_unique R V B hB
  (inner_near_set hB a C d) inner_near_sets_shrink c e
  (inner_nearest_in_near_sets hc) (inner_nearest_in_near_sets he)).
Qed.
End Intersection.
