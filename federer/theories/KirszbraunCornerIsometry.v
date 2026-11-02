(** Federer (1969), 2.10.44, printed p. 202: the prescribed finite map is
    Lipschitzian with optimal constant one. Distances between distinct
    source points and their images are both two; diagonal distances are
    zero. Derive this from the three-value specification alone. The source
    metric is explicitly the supremum norm and the target metric is
    explicitly Euclidean. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology lra.
From Federer Require Import NormMetric EuclideanInnerProduct InnerMetric PlaneSupremumNorm
  KirszbraunCorners KirszbraunCornerDistances KirszbraunCornerMapUP
  LipschitzUP LipschitzBasic LipschitzConstant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [kirszbraun_corner_map_isometry]: direct
    distance-preserving property of the three-point
    map in 2.10.44, p. 202. The distance
    two computation is applied only to distinct
    points; equal points have distance zero. *)
Lemma kirszbraun_corner_map_isometry (R : realType)
    (f : plane_supremum_metric R -> inner_metric_space (@euclidean_inner_productP R 2))
    (hf : is_kirszbraun_corner_map f) x y :
  kirszbraun_corner_source x -> kirszbraun_corner_source y ->
    mdist (f x) (f y)=@mdist R [the metricType R of plane_supremum_metric R] x y.
Proof.
have [hs12 [hs13 hs23]] := kirszbraun_corner_pair_distances R.
have [ht12 [ht13 ht23]] := kirszbraun_equilateral_pair_distances R.
have [hf1 hf2 hf3] := hf.
move=> [[->|->]|->] [[->|->]|->];
  rewrite ?hf1 ?hf2 ?hf3 ?mdistxx ?hs12 ?hs13 ?hs23 ?ht12 ?ht13 ?ht23 //;
  by rewrite [LHS]metric_sym [RHS]metric_sym ?hs12 ?hs13 ?hs23 ?ht12 ?ht13 ?ht23.
Qed.

(** Source for [kirszbraun_corner_map_bound_one]: direct
    Lipschitz bound one of 2.10.44, p. 202,
    using the prescribed norms on source and target. *)
Lemma kirszbraun_corner_map_bound_one (R : realType)
    (f : plane_supremum_metric R -> inner_metric_space (@euclidean_inner_productP R 2)) :
  is_kirszbraun_corner_map f ->
    is_metric_lipschitz_bound (@kirszbraun_corner_source R) f 1.
Proof.
move=> hf; split; first exact: ler01.
by move=> x y hx hy; rewrite mul1r (kirszbraun_corner_map_isometry hf hx hy).
Qed.

(** Source for [kirszbraun_corner_map_optimal_one]: direct
    Lip(f)=1 in 2.10.44, p. 202. The
    first two distinct source points force every
    bound to be at least one. The result
    holds for every map satisfying the three values. *)
Lemma kirszbraun_corner_map_optimal_one (R : realType)
    (f : plane_supremum_metric R -> inner_metric_space (@euclidean_inner_productP R 2))
    (hf : is_kirszbraun_corner_map f) (hLip : is_metric_lipschitz (@kirszbraun_corner_source R) f) :
  metric_lipschitz_constant hLip= 1.
Proof.
have hu := metric_lipschitz_constant_minimal hLip (kirszbraun_corner_map_bound_one hf).
have [h1 [h2 h3]] := kirszbraun_corner_members R.
have hl := metric_lipschitz_constant_attained hLip h1 h2.
rewrite (kirszbraun_corner_map_first_law hf) (kirszbraun_corner_map_second_law hf)
  (kirszbraun_corner_pair_distances R).1 (kirszbraun_equilateral_pair_distances R).1 in hl.
apply/eqP; rewrite eq_le; apply/andP; split=> //; lra.
Qed.
