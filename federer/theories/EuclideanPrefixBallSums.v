(** Actual compact convex ball sums in the section
    coefficient argument of Federer (1969), 3.2.45,
    pp. 279–280. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric InnerConvex
  EuclideanLinearMaps ScalarConvexLength MetricClosedBalls EuclideanClosedBallCompact InnerClosedBallConvex
  VectorSetSum VectorSetSumLaws EuclideanVectorSumCompact CompactSetDistanceProfile CompactHausdorffMetric
  HausdorffDistance HausdorffDistanceBasic MetricSetDistanceUP MetricSetDistanceBasic EuclideanPrefixCompression.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [vector_set_sum_inner_convex]: supporting
    convexity of the original Minkowski sums in Federer
    3.2.45, pp. 279–280, as in 3.2.41,
    p. 278. Interpolate the two original endpoints
    in each factor and rearrange the actual vector
    addition. Empty factors are included. *)
Lemma vector_set_sum_inner_convex (R : realFieldType) (V : lmodType R) (A B : set V) :
  is_inner_convex A -> is_inner_convex B -> is_inner_convex (vector_set_sum A B).
Proof.
move=> hA hB x y /vector_set_sum_membership [a [b [ha [hb ->]]]]
  /vector_set_sum_membership [c [d [hc [hd ->]]]] t ht0 ht1.
apply/vector_set_sum_membership; exists ((1-t)*:a+t*:c),((1-t)*:b+t*:d).
split; first exact: hA a c ha hc t ht0 ht1.
split; first exact: hB b d hb hd t ht0 ht1.
by rewrite !scalerDr addrACA.
Qed.

(** Source for [euclidean_prefix_ball_image_geometry]: supporting
    admissibility of each actual anisotropic ball in Federer
    3.2.45, pp. 279–280. Its original closed
    radius-r ball is compact and convex; the prescribed
    diagonal linear map preserves those properties and
    sends zero to zero. Every real scaling and
    every nonnegative radius, including zero, are retained. *)
Lemma euclidean_prefix_ball_image_geometry (R : realType) n m (h r : R) :
  0<=r ->
  let B : set (inner_metric_space (@euclidean_inner_productP R n)) :=
    [set x | inner_norm (@euclidean_inner_productP R n) x<=r] in
  let D := @euclidean_diagonal_map R n (fun j => if (j<m)%N then h else 1) in
  D @` B !=set0 /\ @compact (inner_metric_space (@euclidean_inner_productP R n)) (D @` B) /\
    is_inner_convex (D @` B).
Proof.
move=> hr B D.
have hBall : B=metric_closed_ball (0 : inner_metric_space (@euclidean_inner_productP R n)) r.
  apply/seteqP; split=> x; by rewrite /B /metric_closed_ball /= inner_metric_distanceE sub0r inner_normN.
have hCompact : compact B by rewrite hBall; exact: euclidean_closed_metric_ball_compact.
have hConvex : is_inner_convex B by rewrite hBall; exact: inner_metric_closed_ball_convex.
split.
- exists (D 0); exists 0=> //; by rewrite /B /= inner_norm0.
- split; last exact: linear_image_inner_convex hConvex.
  exact: continuous_compact (continuous_subspaceT (@euclidean_linear_continuous R n D)) hCompact.
Qed.

(** Source for [euclidean_prefix_ball_sum_geometry]: supporting
    original compact convex domains for the volume limit
    in Federer 3.2.45, pp. 279–280. Sum the
    prescribed diagonal image of the closed ball with
    the original compact convex K. Compactness uses
    the already proved continuous image of a compact
    product; no interior or positive-volume premise occurs. *)
Lemma euclidean_prefix_ball_sum_geometry (R : realType) n m
    (K : set (inner_metric_space (@euclidean_inner_productP R n))) (h r : R) :
  K !=set0 -> compact K -> is_inner_convex K -> 0<=r ->
  let B : set (inner_metric_space (@euclidean_inner_productP R n)) :=
    [set x | inner_norm (@euclidean_inner_productP R n) x<=r] in
  let S := vector_set_sum K
    ((@euclidean_diagonal_map R n (fun j => if (j<m)%N then h else 1)) @` B) in
  S !=set0 /\ compact S /\ is_inner_convex S.
Proof.
move=> hNonempty hCompact hConvex hr B S.
have [hDNonempty [hDCompact hDConvex]] := @euclidean_prefix_ball_image_geometry R n m h r hr.
split; first exact: (vector_set_sum_nonempty _ _).2 (conj hNonempty hDNonempty).
split; [exact: euclidean_vector_sum_compact hCompact hDCompact|
  exact: vector_set_sum_inner_convex hConvex hDConvex].
Qed.

(** Source for [euclidean_prefix_ball_sum_hausdorff_bound]: supporting
    actual anisotropic limit in Federer 3.2.45,
    pp. 279–280, using the Hausdorff distance of
    2.10.21, p. 183. The vertical-ball sum A
    lies in every compressed-ball sum C. Each point
    of C has the same K centre and an original
    vertical foot in A, at distance at most h*r.
    Only the exact set identities are supplied; the
    distance bound is proved from the original norm
    laws. Thin bodies and both empty coordinate blocks
    remain. No limiting-volume equality is assumed. *)
Theorem euclidean_prefix_ball_sum_hausdorff_bound (R : realType) n m
    (K : set (inner_metric_space (@euclidean_inner_productP R n))) (h r : R)
    (A C : compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n))) :
  0<=h -> 0<=r ->
  val A=vector_set_sum K ((@euclidean_diagonal_map R n (fun j => if (j<m)%N then 0 else 1)) @`
    [set x | inner_norm (@euclidean_inner_productP R n) x<=r]) ->
  val C=vector_set_sum K ((@euclidean_diagonal_map R n (fun j => if (j<m)%N then h else 1)) @`
    [set x | inner_norm (@euclidean_inner_productP R n) x<=r]) ->
  mdist A C<=h*r.
Proof.
move=> hh hr hA hC.
pose D0 := @euclidean_diagonal_map R n (fun j => if (j<m)%N then 0 else 1).
pose Dh := @euclidean_diagonal_map R n (fun j => if (j<m)%N then h else 1).
pose B : set (inner_metric_space (@euclidean_inner_productP R n)) :=
  [set x | inner_norm (@euclidean_inner_productP R n) x<=r].
have hSubset : val A `<=` val C.
  rewrite hA hC; move=> x /vector_set_sum_membership [a [b [ha [[z hz <-] ->]]]].
  apply: vector_set_sum_contains ha _; exists (D0 z).
  - change (is_true (inner_norm (@euclidean_inner_productP R n) (D0 z)<=r)).
    exact: le_trans (@euclidean_prefix_zero_norm_bound R n m z) hz.
  - exact: euclidean_prefix_zero_fixed.
rewrite compact_hausdorff_distanceE.
apply: (hausdorff_distance_directed_bound (@hausdorff_distance_specification R _) A C
  (mulr_ge0 hh hr)).2; split.
- move=> x hx; rewrite (compact_set_distance_profile_zero C x).2 //.
  + exact: mulr_ge0 hh hr.
  + exact: hSubset hx.
- move=> x; rewrite hC=> /vector_set_sum_membership [a [b [ha [[z hz <-] ->]]]].
  have hMember : val A (a+D0 z).
    rewrite hA; apply: vector_set_sum_contains ha _; by exists z.
  have hDistance := metric_set_distance_lower (compact_set_distance_profile_specification A) (a+Dh z) hMember.
  have hDifference : (a+Dh z)-(a+D0 z)=Dh z-D0 z by rewrite opprD addrACA subrr add0r.
  rewrite inner_metric_distanceE hDifference in hDistance.
  apply: le_trans hDistance _.
  apply: le_trans (@euclidean_prefix_compression_difference R n m h z) _.
  rewrite (ger0_norm hh).
  have hzBound : inner_norm (@euclidean_inner_productP R n) z<=r := hz.
  have hScaled := ler_wpM2l hh hzBound.
  exact hScaled.
Qed.
