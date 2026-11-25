(** Federer (1969), 3.2.35, p. 272:
    projection commutes with the original positive
    distance tubes. The support below works for
    arbitrary nonempty sources and every cutoff. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  EuclideanProjectionMetric ProjectionImageLifting MetricSetDistanceUP MetricSetDistanceClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [projection_distance_le]: supporting
    contraction of actual set distance in Federer
    3.2.35, p. 272. The two independent
    greatest-lower-bound specifications and the actual
    projection contraction suffice, without closest
    points or source closedness. *)
Lemma projection_distance_le (R:realType) n m
    (p:orthogonal_projection_metric_space R n m)
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) d e:
  is_metric_set_distance S d ->
  @is_metric_set_distance R [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]
    (euclidean_projection_linear p @` S) e ->
  forall x,e (euclidean_projection_linear p x)<=d x.
Proof.
move=>hD hE x.
apply:(@metric_set_distance_greatest R _ S d hD x _)=>a ha.
have hMember:(euclidean_projection_linear p @` S) (euclidean_projection_linear p a) by exists a.
have hLower:=@metric_set_distance_lower R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]
  (euclidean_projection_linear p @` S) e hE (euclidean_projection_linear p x)
  (euclidean_projection_linear p a) hMember.
have hContraction:=@euclidean_projection_nonexpanding R n m p x a.
exact (le_trans hLower hContraction).
Qed.

(** Source for [projection_distance_tube]: the
    literal projected distance-sublevel identity in
    Federer 3.2.35, p. 272. Infimum
    approximation supplies an original source point,
    and the proved exact-distance lift supplies a
    preimage at precisely the target displacement.
    Convexity, boundedness, closedness and source
    measurability are unnecessary for this helper. *)
Theorem projection_distance_tube (R:realType) n m
    (p:orthogonal_projection_metric_space R n m)
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) d e (r:R):
  is_metric_set_distance S d ->
  @is_metric_set_distance R [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]
    (euclidean_projection_linear p @` S) e ->
  euclidean_projection_linear p @` [set x|d x<r]=[set y|e y<r].
Proof.
move=>hD hE; apply/seteqP; split=>y.
- move=>[x hx <-]; exact:(le_lt_trans (@projection_distance_le R n m p S d e hD hE x) hx).
- move=>hy.
  have hError:0<r-e y by rewrite subr_gt0.
  have [z [[a ha hza] hNear]]:=metric_set_distance_approximation hE y hError.
  rewrite addrC subrK in hNear; rewrite -hza in hNear.
  have [x [hpx hDistance]]:=@orthogonal_projection_exact_distance_lift R n m p a y.
  exists x; last exact hpx.
  have hLower:=@metric_set_distance_lower R _ S d hD x a ha.
  apply:(le_lt_trans hLower _).
  by rewrite metric_sym hDistance metric_sym.
Qed.
