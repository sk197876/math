(** Federer (1969), 2.10.44, printed p. 202: no extension of the displayed
    map to S union {0} preserves its Lipschitz constant one. The origin is
    at supremum-norm distance one from all source points. Its image would
    therefore belong to the three disjoint unit-ball constraints already
    proved impossible in the Euclidean target. This argument uses only
    abstract map and norm laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import NormMetric EuclideanInnerProduct InnerMetric PlaneSupremumNorm
  KirszbraunCorners KirszbraunCornerDistances KirszbraunCornerMapUP
  EquilateralUnitBallsEmpty LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [kirszbraun_corner_distance_origin]: direct
    mu(u)=1 for u in S in 2.10.44,
    p. 202, expressed as the distance from
    the additional source point zero. *)
Lemma kirszbraun_corner_distance_origin (R : realType) (x : plane_supremum_metric R) :
  kirszbraun_corner_source x ->
    @mdist R [the metricType R of plane_supremum_metric R] 0 x= 1.
Proof.
move=> hx; rewrite metric_sym real_norm_metric_distanceE subr0.
exact: kirszbraun_corner_radius_one hx.
Qed.

(** Source for [kirszbraun_corner_map_no_extension]: direct
    impossibility of extending the printed three
    prescribed values with bound one to S union
    {0}, in 2.10.44, p. 202. The
    supremum source metric and Euclidean target
    metric are retained in the bound predicate. *)
Theorem kirszbraun_corner_map_no_extension (R : realType)
    (f : plane_supremum_metric R -> inner_metric_space (@euclidean_inner_productP R 2)) :
  is_kirszbraun_corner_map f ->
    ~ exists g : plane_supremum_metric R -> inner_metric_space (@euclidean_inner_productP R 2),
      (forall x, kirszbraun_corner_source x -> g x=f x) /\
      is_metric_lipschitz_bound ((@kirszbraun_corner_source R) `|` [set 0]) g 1.
Proof.
move=> hf [g [hag [_ hbound]]].
have h0 : ((@kirszbraun_corner_source R) `|` [set 0]) 0 by right.
have hb x (hx : kirszbraun_corner_source x) : mdist (g 0) (f x)<=1.
  have hh := hbound 0 x h0 (or_introl hx).
  by rewrite (hag x hx) mul1r (kirszbraun_corner_distance_origin hx) in hh.
have [h1 [h2 h3]] := kirszbraun_corner_members R.
have hb1 := hb _ h1; have hb2 := hb _ h2; have hb3 := hb _ h3.
rewrite (kirszbraun_corner_map_first_law hf) in hb1.
rewrite (kirszbraun_corner_map_second_law hf) in hb2.
rewrite (kirszbraun_corner_map_third_law hf) in hb3.
apply: (@kirszbraun_three_unit_balls_empty R).
by exists (g 0).
Qed.
