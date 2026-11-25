(** Federer (1969), 2.2.8, p. 64: sealed branch map g. The signature exposes
    only its branch membership specification. Source context and encoding:
    ClosedCoverTreeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import SequenceSpace CompleteMetricUP ClosedCoverTreeUP
  ClosedCoverMapUP ClosedCoverMapConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type ClosedCoverMapSignature.
(** Source for [value]: Federer 2.2.8, p. 64, the map from
    positive-integer sequences into the complete target space. *)
Parameter value : forall (R : realType) (T : metricType R),
  is_complete_metric_space T -> forall E : seq nat -> set T,
  is_closed_cover_tree E -> positive_sequence_space R -> T.
(** Source for [laws]: Federer 2.2.8, p. 64, each g(n)
    belongs to all closed sets on the corresponding branch. *)
Parameter laws : forall (R : realType) (T : metricType R)
  (hT : is_complete_metric_space T) (E : seq nat -> set T)
  (hE : is_closed_cover_tree E), is_closed_cover_map E (@value R T hT E hE).
End ClosedCoverMapSignature.
Module ClosedCoverMap : ClosedCoverMapSignature.
(** Source for [value]: supporting private witness selection
    for Federer 2.2.8, p. 64, from the proved map existence theorem. *)
Definition value (R : realType) (T : metricType R)
    (hT : is_complete_metric_space T) (E : seq nat -> set T)
    (hE : is_closed_cover_tree E) :=
  projT1 (cid (closed_cover_map_exists hT hE)).
(** Source for [laws]: Federer 2.2.8, p. 64, the selected
    map discharges its abstract branch membership specification. *)
Lemma laws (R : realType) (T : metricType R)
    (hT : is_complete_metric_space T) (E : seq nat -> set T)
    (hE : is_closed_cover_tree E) : is_closed_cover_map E (@value R T hT E hE).
Proof. exact: projT2 (cid (closed_cover_map_exists hT hE)). Qed.
End ClosedCoverMap.
