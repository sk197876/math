(** Federer (1969), 4.1.16, pp. 373–374: apply the
    original closed-convex nearest map to a compact hull in
    the actual norm topology of currents. The identity
    between the two metric presentations is isometric; no
    external projection theorem is used. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric InnerConvex HilbertFormCompactness
  NormMetric NormMetricScaleContinuity EuclideanConvexNearestMapUP
  EuclideanConvexNearestMapSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section EuclideanCompactNearestMap.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation hB := (@euclidean_inner_productP R n).
Local Notation hN := (inner_norm_real_norm hB).
Local Notation XT := (real_norm_metric_space hN).
Local Notation IT := (inner_metric_space hB).
Variable C : set X.
Hypothesis hCompact : @compact XT C.

(** Source for [euclidean_compact_set_inner_closed]: compact
    Euclidean C is closed in the original inner-product
    metric, supporting the nearest map of 4.1.16, p. 374.
    The norm and inner-product metrics have the same distance. *)
Lemma euclidean_compact_set_inner_closed : @closed IT C.
Proof.
have hIdentity : continuous (fun x:XT=>(x:IT)).
  apply: (@metric_fixed_lipschitz_continuous R XT IT (fun x=>x) 1 ler01).
  by move=> x y; rewrite inner_metric_distanceE real_norm_metric_distanceE mul1r.
have hImage : (fun x:XT=>(x:IT)) @` C=C by rewrite image_id.
have hCompactInner : @compact IT C.
  rewrite -hImage.
  exact: (continuous_compact (continuous_subspaceT hIdentity) hCompact).
exact: (compact_closed (@metric_hausdorff R IT) hCompactInner).
Qed.

(** Source for [euclidean_compact_convex_nearest_map]: the
    already opaque nearest map of 4.1.16, p. 373,
    applied to a nonempty compact convex C in the current
    norm topology. This is an abbreviation; its witness
    remains hidden behind the existing nearest-map signature. *)
Definition euclidean_compact_convex_nearest_map
    (hNonempty : C !=set0) (hConvex : is_inner_convex C) : X -> X :=
  @EuclideanConvexNearestMap.value R n C euclidean_compact_set_inner_closed
    hNonempty hConvex.

(** Source for [euclidean_compact_convex_nearest_map_laws]:
    this map has the original minimizing relation,
    supporting Federer 4.1.16, p. 374. *)
Lemma euclidean_compact_convex_nearest_map_laws
    (hNonempty : C !=set0) (hConvex : is_inner_convex C) :
  is_euclidean_convex_nearest_map C
    (euclidean_compact_convex_nearest_map hNonempty hConvex).
Proof. exact: EuclideanConvexNearestMap.laws. Qed.
End EuclideanCompactNearestMap.
