(** Federer (1969), 4.1.18, pp. 375–376: reuse
    the existing opaque set sum and closed-ball laws
    for the original support tubes. For closed nonempty
    Euclidean sets this is exactly the printed distance
    sublevel; the empty support has an empty tube. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerNormInequalities InnerMetric VectorSetSum
  EuclideanVectorSumCompact MetricClosedBalls EuclideanClosedBallCompact
  MetricSetDistanceUP CompactConvexClosedTubePolynomial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section EuclideanClosedSupportTube.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation hB := (@euclidean_inner_productP R n).
Local Notation E := (inner_metric_space hB).
Local Notation N := (inner_norm hB).

(** Source for [euclidean_closed_support_tube]: the closed
    epsilon neighbourhood of a support in Federer 4.1.18,
    pp. 375-376. This alias uses the earlier opaque sum;
    its distance-sublevel identity is proved separately. *)
Definition euclidean_closed_support_tube (A : set X) (r : R) : set X :=
  vector_set_sum A [set v | N v<=r].

(** Source for [euclidean_closed_support_tube_empty]: the
    zero current's empty support stays empty under every
    smoothing radius, supporting Federer 4.1.18, p. 375. *)
Lemma euclidean_closed_support_tube_empty r :
  euclidean_closed_support_tube set0 r=set0.
Proof.
apply/seteqP; split; last by move=> x [].
by move=> x /vector_set_sum_membership [a [b []]].
Qed.

(** Source for [euclidean_closed_support_tube_includes]:
    each support lies in its nonnegative-radius closed tube,
    supporting Federer 4.1.18, pp. 375-376. *)
Lemma euclidean_closed_support_tube_includes A r :
  0<=r -> A `<=` euclidean_closed_support_tube A r.
Proof.
move=> hr x hx.
have hZero : N 0<=r by rewrite inner_norm0.
have hMember : vector_set_sum A [set v : X | N v<=r] (x+0) :=
  @vector_set_sum_contains X A [set v : X | N v<=r] x 0 hx hZero.
by rewrite addr0 in hMember.
Qed.

(** Source for [euclidean_closed_support_tube_mono]: enlarging
    a support or its radius enlarges the printed tube,
    supporting the nested K_i in Federer 4.1.18, p. 376. *)
Lemma euclidean_closed_support_tube_mono A B r s :
  A `<=` B -> r<=s ->
  euclidean_closed_support_tube A r `<=`
    euclidean_closed_support_tube B s.
Proof.
move=> hAB hrs x /vector_set_sum_membership [a [b [ha [hb ->]]]].
apply: vector_set_sum_contains; first exact: hAB a ha.
exact: le_trans hb hrs.
Qed.

(** Source for [euclidean_closed_support_tube_nested]: the
    nested-radius inclusion used to contain every K_i in
    the closed delta/2 tube, Federer 4.1.18, p. 376.
    Empty source sets require no special point choice. *)
Lemma euclidean_closed_support_tube_nested A r s :
  euclidean_closed_support_tube (euclidean_closed_support_tube A r) s
    `<=` euclidean_closed_support_tube A (r+s).
Proof.
move=> x /vector_set_sum_membership [u [v [hu [hv hx]]]].
have [a [b [ha [hb huab]]]] :=
  (@vector_set_sum_membership X A [set w : X | N w<=r] u).1 hu.
apply/vector_set_sum_membership; exists a,(b+v); split; first exact: ha.
split.
- exact: le_trans (inner_norm_triangle hB b v) (lerD hb hv).
- by rewrite hx huab addrA.
Qed.

(** Source for [euclidean_closed_support_tube_compact]: every
    closed finite-radius tube around an original compact K
    is compact, supporting K, E and C in Federer 4.1.18,
    pp. 375-376. Empty K and dimension zero are included. *)
Lemma euclidean_closed_support_tube_compact (A : set E) r :
  compact A -> compact (euclidean_closed_support_tube A r : set E).
Proof.
move=> hA; rewrite /euclidean_closed_support_tube.
apply:(@euclidean_vector_sum_compact R n A _ hA).
have hBall : [set y : E | N y<=r]=metric_closed_ball (0:E) r.
  apply/seteqP; split=> y hy.
  - change (is_true (mdist (0:E) y<=r)).
    rewrite inner_metric_distanceE sub0r inner_normN; exact: hy.
  - change (is_true (mdist (0:E) y<=r)) in hy.
    by rewrite inner_metric_distanceE sub0r inner_normN in hy.
rewrite hBall; exact: euclidean_closed_metric_ball_compact.
Qed.

(** Source for [euclidean_closed_support_tube_distance]: the
    alias is exactly {x:dist(x,A)<=r} for the original
    closed nonempty Euclidean support, Federer 4.1.18,
    pp. 375-376, by the earlier nearest-point tube identity. *)
Lemma euclidean_closed_support_tube_distance (A : set E) d r :
  closed A -> A !=set0 -> is_metric_set_distance A d ->
  euclidean_closed_support_tube A r=[set x | d x<=r].
Proof.
move=> hClosed hNonempty hDistance.
exact: esym (@euclidean_closed_ball_vector_sum_tube R n A d r
  hClosed hNonempty hDistance).
Qed.
End EuclideanClosedSupportTube.
