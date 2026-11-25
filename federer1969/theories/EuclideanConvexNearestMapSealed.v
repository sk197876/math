(** Opaque nearest-point map for Federer (1969),
    4.1.16, pp. 373-374. The public map inherits only
    the independent nearest-point law. All retraction and
    Lipschitz conclusions are derived later. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric InnerConvex EuclideanConvexNearestMapUP
  EuclideanConvexNearestMapExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module Type EuclideanConvexNearestMapSignature.
(** Source for [value]: the nearest-point map for the
    original nonempty closed convex C, Federer 4.1.16,
    p. 373. Dimension zero and unbounded C are allowed. *)
Parameter value : forall (R : realType) n
    (C : set (inner_metric_space (@euclidean_inner_productP R n))),
  closed C -> C !=set0 -> is_inner_convex C -> R_n R n -> R_n R n.
(** Source for [laws]: every chosen value satisfies the
    original nearest-point law, Federer 4.1.16, p. 373. *)
Parameter laws : forall (R : realType) n
    (C : set (inner_metric_space (@euclidean_inner_productP R n)))
    (hClosed : closed C) (hNonempty : C !=set0)
    (hConvex : is_inner_convex C),
  is_euclidean_convex_nearest_map C
    (@value R n C hClosed hNonempty hConvex).
End EuclideanConvexNearestMapSignature.

Module EuclideanConvexNearestMap : EuclideanConvexNearestMapSignature.
(** Source for [value]: hide a separately proved nearest
    witness, supporting Federer 4.1.16, p. 373. *)
Definition value (R : realType) n
    (C : set (inner_metric_space (@euclidean_inner_productP R n)))
    (hClosed : closed C) (hNonempty : C !=set0)
    (hConvex : is_inner_convex C) : R_n R n -> R_n R n :=
  projT1 (cid (@euclidean_convex_nearest_map_exists R n C
    hClosed hNonempty)).
(** Source for [laws]: the opaque map has precisely the
    original minimising laws, Federer 4.1.16, p. 373. *)
Lemma laws (R : realType) n
    (C : set (inner_metric_space (@euclidean_inner_productP R n)))
    (hClosed : closed C) (hNonempty : C !=set0)
    (hConvex : is_inner_convex C) :
  is_euclidean_convex_nearest_map C
    (@value R n C hClosed hNonempty hConvex).
Proof.
exact: (projT2 (cid (@euclidean_convex_nearest_map_exists R n C
  hClosed hNonempty))).
Qed.
End EuclideanConvexNearestMap.
