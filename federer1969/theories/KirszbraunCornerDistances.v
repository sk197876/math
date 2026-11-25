(** Federer (1969), 2.10.44, printed p. 202, first example: all source
    points have mu-norm one, and distinct source points and their prescribed
    images have distance two. The printed distance-two sentence needs
    distinct points; the diagonal has distance zero. This local
    qualification is not an erratum entry. The computations use only public
    coordinate and opaque norm laws. Source context: KirszbraunCorners.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology ring lra.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanRealPlane
  NormMetric PlaneSupremumNorm PlanePairNormGeometry KirszbraunCorners.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [kirszbraun_corner_radius_one]: direct
    mu(u)=1 for u in the printed source S
    in 2.10.44, p. 202. *)
Lemma kirszbraun_corner_radius_one (R : realType) (x : plane_supremum_metric R) :
  kirszbraun_corner_source x -> plane_supremum_norm x= 1.
Proof.
move=> [[->|->]|->];
  by rewrite /kirszbraun_corner_first /kirszbraun_corner_second /kirszbraun_corner_third
    plane_supremum_normE !real_plane_pair_first_coordinate !real_plane_pair_second_coordinate
    ?normrN normr1 maxxx.
Qed.

(** Source for [kirszbraun_corner_pair_distances]: direct
    mu(u-v)=2 for the three distinct unordered
    source pairs in 2.10.44, p. 202. *)
Lemma kirszbraun_corner_pair_distances (R : realType) :
  @mdist R [the metricType R of plane_supremum_metric R]
    (kirszbraun_corner_first R) (kirszbraun_corner_second R)= 2 /\
  @mdist R [the metricType R of plane_supremum_metric R]
    (kirszbraun_corner_first R) (kirszbraun_corner_third R)= 2 /\
  @mdist R [the metricType R of plane_supremum_metric R]
    (kirszbraun_corner_second R) (kirszbraun_corner_third R)= 2.
Proof.
have hpm : (1:R)-(-1)= 2 by ring.
have hmp : (-1:R)-1= -2 by ring.
split.
- by rewrite /kirszbraun_corner_first /kirszbraun_corner_second supremum_plane_pair_distance
    hpm hmp normrN normr_nat maxxx.
- split.
  + by rewrite /kirszbraun_corner_first /kirszbraun_corner_third supremum_plane_pair_distance
      subrr normr0 hmp normrN normr_nat max_r // ler0n.
  + by rewrite /kirszbraun_corner_second /kirszbraun_corner_third supremum_plane_pair_distance
      subrr normr0 hmp normrN normr_nat max_l // ler0n.
Qed.

(** Source for [kirszbraun_equilateral_pair_distances]: direct
    nu(f(u)-f(v))=2 for distinct prescribed images
    in 2.10.44, p. 202. The height sqrt(3)
    is verified using the actual Euclidean metric. *)
Lemma kirszbraun_equilateral_pair_distances (R : realType) :
  mdist (kirszbraun_equilateral_first R) (kirszbraun_equilateral_second R)= 2 /\
  mdist (kirszbraun_equilateral_first R) (kirszbraun_equilateral_third R)= 2 /\
  mdist (kirszbraun_equilateral_second R) (kirszbraun_equilateral_third R)= 2.
Proof.
have hsqrt : (Num.sqrt (3:R))^+2= 3 by rewrite sqr_sqrtr // ler0n.
have hdist (p q : inner_metric_space (@euclidean_inner_productP R 2)) :
    mdist p q^+2= 4 -> mdist p q= 2.
  move=> hs; have hh := mdist_ge0 p q; nra.
split.
- apply: hdist; rewrite euclidean_plane_squared_distance_coordinates
    /kirszbraun_equilateral_first /kirszbraun_equilateral_second
    !real_plane_pair_first_coordinate !real_plane_pair_second_coordinate; ring.
- split.
  + apply: hdist; rewrite euclidean_plane_squared_distance_coordinates
      /kirszbraun_equilateral_first /kirszbraun_equilateral_third
      !real_plane_pair_first_coordinate !real_plane_pair_second_coordinate; nra.
  + apply: hdist; rewrite euclidean_plane_squared_distance_coordinates
      /kirszbraun_equilateral_second /kirszbraun_equilateral_third
      !real_plane_pair_first_coordinate !real_plane_pair_second_coordinate; nra.
Qed.

(** Source for [kirszbraun_printed_two_needs_distinct]: local
    diagonal counterexample to the literal unqualified
    distance-two sentence in 2.10.44, p. 202.
    The first printed source point belongs to S
    but its distance to itself is zero. This
    is separate from Federer's published erratum. *)
Theorem kirszbraun_printed_two_needs_distinct (R : realType) :
  ~ (forall x y, kirszbraun_corner_source x -> kirszbraun_corner_source y ->
    @mdist R [the metricType R of plane_supremum_metric R] x y= 2).
Proof.
move=> htwo.
have ha := (kirszbraun_corner_members R).1.
have hh := htwo (kirszbraun_corner_first R) (kirszbraun_corner_first R) ha ha.
rewrite mdistxx in hh.
have hpos : (0:R)<2 by rewrite ltr0n.
by rewrite -hh ltxx in hpos.
Qed.
