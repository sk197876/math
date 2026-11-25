(** Laws for Federer (1969), 4.1.16, pp. 373-374.
    Every assertion consumes the independent nearest-point
    law and previously proved inner-product results. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology ring lra.
From Federer Require Import InnerProductUP GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric InnerConvex InnerNearestUP InnerSetDistanceUP
  InnerSetDistance Bilinear BilinearNegation InnerProductLaws NearestConvexVariational
  InnerNearestContraction LipschitzUP EuclideanConvexNearestMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section EuclideanConvexNearestMapLaws.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation B := (@euclidean_inner_product R n).
Local Notation hB := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm hB).
Variable C : set X.
Variable P : X -> X.
Hypothesis hP : is_euclidean_convex_nearest_map C P.

(** Source for [euclidean_convex_nearest_map_range]: the
    original map has values in C, Federer 4.1.16, p. 373. *)
Lemma euclidean_convex_nearest_map_range x : C (P x).
Proof. exact: inner_nearest_member_law (hP x). Qed.

(** Source for [euclidean_convex_nearest_map_fixed]: the
    original map retracts onto C, Federer 4.1.16, p. 373.
    For x in C the nearest distance is zero. *)
Lemma euclidean_convex_nearest_map_fixed x : C x -> P x=x.
Proof.
move=> hx.
have hBound := inner_nearest_minimal_law (hP x) hx.
rewrite subrr inner_norm0 in hBound.
have hZero : N (x-P x)=0.
  by apply/le_anti; rewrite hBound inner_norm_nonnegative.
have hEqual : x = P x.
  by move/eqP: hZero; rewrite inner_norm_eq0 subr_eq0 => /eqP.
exact: esym hEqual.
Qed.

(** Source for [euclidean_convex_nearest_map_distance]: the
    original nearest-point distance equality, Federer 4.1.16,
    p. 373, using the earlier sealed distance to C. *)
Lemma euclidean_convex_nearest_map_distance (hNonempty : C !=set0) x :
  N (x-P x)=inner_set_distance hB x hNonempty.
Proof.
exact: esym (inner_nearest_distance
  (inner_set_distanceP hB x hNonempty) (hP x)).
Qed.

Hypothesis hConvex : is_inner_convex C.

(** Source for [euclidean_convex_nearest_map_graph]: the
    original relation consists exactly of the pairs (x,y)
    with y in C and |x-y|=dist(x,C), Federer 4.1.16,
    p. 373. The displayed relation is therefore precisely
    the graph of the specified map. *)
Theorem euclidean_convex_nearest_map_graph
    (hNonempty : C !=set0) x y :
  P x=y <-> C y /\ N (x-y)=inner_set_distance hB x hNonempty.
Proof.
split.
- move=> <-; split; first exact: euclidean_convex_nearest_map_range.
  exact: euclidean_convex_nearest_map_distance.
- move=> [hy hDistance].
  have hNearest : is_inner_nearest hB x C y.
    constructor; first exact: hy.
    move=> z hz; rewrite hDistance.
    exact: (@inner_set_distance_lower_law R X B hB x C
      (@inner_set_distance R X B hB x C hNonempty)
      (@inner_set_distanceP R X B hB x C hNonempty) z hz).
  have hBound := @inner_nearest_pair_nonexpanding R X B hB C
    x x (P x) y hConvex (hP x) hNearest.
  rewrite subrr inner_norm0 in hBound.
  have hZero : N (P x-y)=0.
    by apply/le_anti; rewrite hBound inner_norm_nonnegative.
  by move/eqP: hZero; rewrite inner_norm_eq0 subr_eq0 => /eqP.
Qed.

(** Source for [euclidean_convex_nearest_map_variational]:
    (x-y).(y-v)>=0 for y=P(x), v in C, Federer 4.1.16,
    p. 374. Reuse the earlier segment quadratic argument. *)
Lemma euclidean_convex_nearest_map_variational x v :
  C v -> 0<=B (x-P x) (P x-v).
Proof.
move=> hv.
have hBound := @inner_nearest_convex_variational R X B hB
  C hConvex x (P x) (hP x) v hv.
rewrite -[P x-v]opprB (bilNr (inner_bilinear hB)) oppr_ge0.
exact: hBound.
Qed.

(** Source for [euclidean_convex_nearest_map_pair_lower_bound]:
    (x-u).(y-v)>=(y-v).(y-v), with y=P(x), v=P(u),
    Federer 4.1.16, p. 374. The two preceding variational
    inequalities are combined by the printed bilinear identity. *)
Lemma euclidean_convex_nearest_map_pair_lower_bound x u :
  B (P x-P u) (P x-P u)<=B (x-u) (P x-P u).
Proof.
have hFirst := euclidean_convex_nearest_map_variational x
  (euclidean_convex_nearest_map_range u).
have hSecond := euclidean_convex_nearest_map_variational u
  (euclidean_convex_nearest_map_range x).
rewrite -[P u-P x]opprB (bilNr (inner_bilinear hB))
  oppr_ge0 in hSecond.
have hExpansion : B (x-u) (P x-P u)=
    B (P x-P u) (P x-P u)+B (x-P x) (P x-P u)
      -B (u-P u) (P x-P u).
  rewrite !(bilBl (inner_bilinear hB)); ring.
rewrite hExpansion; lra.
Qed.

(** Source for [euclidean_convex_nearest_map_nonexpanding]:
    |x-u|>=|P(x)-P(u)|, Federer 4.1.16, p. 374.
    The earlier nearest-pair theorem proves this exact inequality. *)
Theorem euclidean_convex_nearest_map_nonexpanding x u :
  N (P x-P u)<=N (x-u).
Proof.
exact: (@inner_nearest_pair_nonexpanding R X B hB C
  x u (P x) (P u) hConvex (hP x) (hP u)).
Qed.

(** Source for [euclidean_convex_nearest_map_lipschitz]:
    Lip(P)<= 1, Federer 4.1.16, p. 373. The map is on
    all of Euclidean space and C need not be bounded. *)
Theorem euclidean_convex_nearest_map_lipschitz :
  is_metric_lipschitz_bound setT
    (P : inner_metric_space hB -> inner_metric_space hB) 1.
Proof.
split; first exact: ler01.
move=> x u _ _; rewrite mul1r !inner_metric_distanceE.
exact: euclidean_convex_nearest_map_nonexpanding.
Qed.
End EuclideanConvexNearestMapLaws.
