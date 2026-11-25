(** Federer (1969), 4.1.16, pp. 373–374: the displayed
    segment minimum and its exact quadratic expansion. Reuse
    the independently specified nearest-point law and the
    preceding inner-product identities. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals ring.
From Federer Require Import InnerProductUP GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerConvex InnerNearestUP Bilinear InnerProductLaws
  EuclideanConvexNearestMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section EuclideanConvexNearestMapQuadratic.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation B := (@euclidean_inner_product R n).
Local Notation hB := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm hB).

(** Source for [euclidean_nearest_segment_quadratic]: the
    displayed equality in Federer 4.1.16, p. 373.
    The squared distance to the segment point equals the
    squared nearest distance plus the linear and quadratic
    displacement terms. The identity itself holds for every
    real parameter, before the segment restriction is used. *)
Lemma euclidean_nearest_segment_quadratic (x y v : X) (t : R) :
  N (x-((1-t)*:y+t*:v))^+2 =
    N (x-y)^+2+(2*t)*B (x-y) (y-v)+t^+2*N (y-v)^+2.
Proof.
have hSegment : (1-t)*:y+t*:v=y+t*:(v-y).
  by rewrite scalerBl scale1r scalerBr addrAC addrA.
have hDifference : x-((1-t)*:y+t*:v)=(x-y)+t*:(y-v).
  by rewrite hSegment opprD addrA -scalerN opprB.
have hComm : (x-y)+t*:(y-v)=t*:(y-v)+(x-y) by exact: addrC.
rewrite hDifference !inner_norm_sqr hComm (inner_quadratic_expansion hB)
  (inner_symmetric hB (y-v) (x-y)).
ring.
Qed.

Variable C : set X.
Variable P : X -> X.
Hypothesis hP : is_euclidean_convex_nearest_map C P.
Hypothesis hConvex : is_inner_convex C.

(** Source for [euclidean_convex_nearest_map_segment_minimum]:
    the first displayed inequality in Federer 4.1.16,
    p. 373. A point of the segment from P(x) to
    any v in C is in C, so its squared distance
    from x cannot improve the nearest squared distance. *)
Lemma euclidean_convex_nearest_map_segment_minimum x v t :
  C v -> 0<=t<= 1 ->
  N (x-P x)^+2<=N (x-((1-t)*:P x+t*:v))^+2.
Proof.
move=> hv /andP [ht htOne].
have hSegment : C ((1-t)*:P x+t*:v).
  exact: (@hConvex (P x) v (inner_nearest_member_law (hP x))
    hv t ht htOne).
rewrite (ler_sqr (inner_norm_nonnegative hB _)
  (inner_norm_nonnegative hB _)).
exact: (@inner_nearest_minimal_law R X B hB x C (P x) (hP x)
  ((1-t)*:P x+t*:v) hSegment).
Qed.

(** Source for [euclidean_convex_nearest_map_segment_quadratic]:
    the full two-part display in Federer 4.1.16,
    p. 373. Both the minimum and the exact polynomial
    expansion are retained, including t=0 and t= 1. *)
Theorem euclidean_convex_nearest_map_segment_quadratic x v t :
  C v -> 0<=t<= 1 ->
  N (x-P x)^+2<=N (x-((1-t)*:P x+t*:v))^+2 /\
  N (x-((1-t)*:P x+t*:v))^+2 =
    N (x-P x)^+2+(2*t)*B (x-P x) (P x-v)+t^+2*N (P x-v)^+2.
Proof.
move=> hv ht; split.
- exact: euclidean_convex_nearest_map_segment_minimum hv ht.
- exact: euclidean_nearest_segment_quadratic.
Qed.
End EuclideanConvexNearestMapQuadratic.
