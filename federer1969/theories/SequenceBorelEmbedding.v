(** Federer (1969), 2.2.9, p. 65: every complete, nonempty metric space
    without isolated points contains a Borel subset homeomorphic with the
    positive-integer sequence space. This module proves the general
    assertion. The additional real-line countable-complement assertion is a
    separate obligation; it is not asserted by the theorem below. Source
    editions: NoIsolatedPoints.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import SequenceSpace CompleteMetricUP TopologicalBorel
  NoIsolatedPoints HomeomorphismOnto OpenEmbeddingTreeUP OpenEmbeddingTreeSealed
  OpenEmbeddingMapUP OpenEmbeddingMapSealed OpenEmbeddingBorelImage
  OpenEmbeddingImageEquality OpenEmbeddingInjectivity OpenEmbeddingMapContinuous
  OpenEmbeddingOpenness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [complete_nonisolated_sequence_borel_embedding]: direct
    formalisation of the general proposition in Federer 2.2.9, p. 65: a
    complete nonempty metric space without isolated points has a Borel
    subset homeomorphic with the sequence space. No separability or local
    compactness premise is added. The homeomorphism uses the continuous,
    injective, open-map characterization. *)
Theorem complete_nonisolated_sequence_borel_embedding (R : realType) (T : metricType R) :
  is_complete_metric_space T -> has_no_isolated_points T -> (@setT T) !=set0 ->
  exists (G : set T) (g : positive_sequence_space R -> T),
    borel_set G /\ is_homeomorphism_onto G g.
Proof.
move=> hc hno hn.
pose U := @OpenEmbeddingTree.value R T hno hn.
have hU : is_open_embedding_tree U := @OpenEmbeddingTree.laws R T hno hn.
pose g := @OpenEmbeddingMap.value R T hc U hU.
have hg : is_open_embedding_map U g := @OpenEmbeddingMap.laws R T hc U hU.
exists (open_embedding_image U), g; split.
- exact: (@open_embedding_image_borel R T U hU).
- constructor.
  + exact: (@open_embedding_map_injective R T U hU g hg).
  + exact: (@open_embedding_map_image R T U hU g hg).
  + exact: (@open_embedding_map_continuous R T U hU g hg).
  + move=> O ho; exact: (@open_embedding_map_open R T U hU g hg O ho).
Qed.
