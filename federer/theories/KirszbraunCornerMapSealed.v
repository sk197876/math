(** Opaque finite-map witness for Federer (1969), 2.10.44, printed p. 202.
    Expose only the three prescribed source values. The piecewise
    implementation and its off-source values are hidden; nonexpansion and
    nonextension are later proved consequences. Source context:
    KirszbraunCornerMapUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import EuclideanInnerProduct InnerMetric PlaneSupremumNorm
  KirszbraunCornerMapUP KirszbraunCornerMapConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type KIRSZBRAUN_CORNER_MAP.
(** Source for [value]: abstract map f on the
    three corners in 2.10.44, p. 202. *)
Parameter value : forall R : realType, plane_supremum_metric R ->
  inner_metric_space (@euclidean_inner_productP R 2).
(** Source for [laws]: the three original value
    laws of f in 2.10.44, p. 202. *)
Parameter laws : forall R : realType, is_kirszbraun_corner_map (@value R).
End KIRSZBRAUN_CORNER_MAP.
Module KirszbraunCornerMap : KIRSZBRAUN_CORNER_MAP.
(** Source for [value]: privately proved finite-
    map witness for 2.10.44, p. 202,
    hidden by opaque module ascription. *)
Definition value (R : realType) := projT1 (cid (@kirszbraun_corner_map_exists R)).
(** Source for [laws]: proved original-value laws
    of the opaque map in 2.10.44, p. 202. *)
Lemma laws (R : realType) : is_kirszbraun_corner_map (@value R).
Proof. exact: (projT2 (cid (@kirszbraun_corner_map_exists R))). Qed.
End KirszbraunCornerMap.
