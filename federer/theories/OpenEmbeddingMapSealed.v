(** Federer (1969), 2.2.9, p. 65: sealed branch map g. The signature exposes
    only its branch membership specification. Source context and encoding:
    OpenEmbeddingTreeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import SequenceSpace CompleteMetricUP OpenEmbeddingTreeUP
  OpenEmbeddingMapUP OpenEmbeddingMapConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type OpenEmbeddingMapSignature.
(** Source for [value]: Federer 2.2.9, p. 65, the map from
    positive-integer sequences into the complete target space. *)
Parameter value : forall (R : realType) (T : metricType R),
  is_complete_metric_space T -> forall E : seq nat -> set T,
  is_open_embedding_tree E -> positive_sequence_space R -> T.
(** Source for [laws]: Federer 2.2.9, p. 65, each g(n)
    belongs to all closed sets on the corresponding branch. *)
Parameter laws : forall (R : realType) (T : metricType R)
  (hT : is_complete_metric_space T) (E : seq nat -> set T)
  (hE : is_open_embedding_tree E), is_open_embedding_map E (@value R T hT E hE).
End OpenEmbeddingMapSignature.
Module OpenEmbeddingMap : OpenEmbeddingMapSignature.
(** Source for [value]: supporting private witness selection
    for Federer 2.2.9, p. 65, from the proved map existence theorem. *)
Definition value (R : realType) (T : metricType R)
    (hT : is_complete_metric_space T) (E : seq nat -> set T)
    (hE : is_open_embedding_tree E) :=
  projT1 (cid (open_embedding_map_exists hT hE)).
(** Source for [laws]: Federer 2.2.9, p. 65, the selected
    map discharges its abstract branch membership specification. *)
Lemma laws (R : realType) (T : metricType R)
    (hT : is_complete_metric_space T) (E : seq nat -> set T)
    (hE : is_open_embedding_tree E) : is_open_embedding_map E (@value R T hT E hE).
Proof. exact: projT2 (cid (open_embedding_map_exists hT hE)). Qed.
End OpenEmbeddingMap.
