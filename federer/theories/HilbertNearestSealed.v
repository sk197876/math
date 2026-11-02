(** Federer (1969), 1.7.13, p. 37: the nearest point, exposed through its
    minimising laws. The completeness witness remains hidden by opaque
    module ascription. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import InnerProductUP InnerMetric InnerNormedTopology
  InnerConvex InnerNearestUP HilbertSpaceUP HilbertNearestConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type HilbertNearestSig.
(** Source for [point]: Federer 1.7.13, p. 37,
    the specified nearest point of the nonempty closed convex set. *)
Parameter point : forall (R : realType) (V : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B), is_hilbert_space hB ->
  forall (a : inner_metric_space hB) (C : set (inner_metric_space hB)),
  C !=set0 -> closed C -> is_inner_convex C -> V.
(** Source for [laws]: Federer 1.7.13, p. 37,
    membership and distance-minimisation laws of the nearest point. *)
Parameter laws : forall (R : realType) (V : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B) (hH : is_hilbert_space hB)
  (a : inner_metric_space hB) (C : set (inner_metric_space hB))
  (hne : C !=set0) (hclosed : closed C) (hconv : is_inner_convex C),
  is_inner_nearest hB a C (@point R V B hB hH a C hne hclosed hconv).
End HilbertNearestSig.
Module HilbertNearest : HilbertNearestSig.
(** Source for [point]: Federer 1.7.13, p. 37,
    select a proved nearest-point witness inside the sealed module. *)
Definition point (R : realType) (V : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B) (hH : is_hilbert_space hB)
  (a : inner_metric_space hB) (C : set (inner_metric_space hB))
  (hne : C !=set0) (hclosed : closed C) (hconv : is_inner_convex C) : V :=
  sval (constructive_indefinite_description
    (@hilbert_nearest_exists R V B hB hH a C hne hclosed hconv)).
(** Source for [laws]: Federer 1.7.13, p. 37,
    the selected witness satisfies the exposed minimisation laws. *)
Lemma laws (R : realType) (V : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B) (hH : is_hilbert_space hB)
  (a : inner_metric_space hB) (C : set (inner_metric_space hB))
  (hne : C !=set0) (hclosed : closed C) (hconv : is_inner_convex C) :
  is_inner_nearest hB a C (@point R V B hB hH a C hne hclosed hconv).
Proof. exact: (svalP (constructive_indefinite_description
    (@hilbert_nearest_exists R V B hB hH a C hne hclosed hconv))). Qed.
End HilbertNearest.
