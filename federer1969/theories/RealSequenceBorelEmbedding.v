(** Federer (1969), 2.2.9, p. 65: the real line has a Borel subset with
    countable complement homeomorphic to the positive-integer sequence
    space. This proof combines the sealed interval tree with the general
    branch-map interface; no implementation of either witness is unfolded.
    Source context: NoIsolatedPoints.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets cardinality reals topology.
From Federer Require Import SequenceSpace TopologicalBorel HomeomorphismOnto
  RealMetricBackground RealMetricCompleteness RealIntervalTreeUP RealIntervalTreeSealed
  OpenEmbeddingTreeUP OpenEmbeddingCountableComplement OpenEmbeddingBorelImage
  OpenEmbeddingMapUP OpenEmbeddingMapSealed OpenEmbeddingImageEquality
  OpenEmbeddingInjectivity OpenEmbeddingMapContinuous OpenEmbeddingOpenness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [real_sequence_borel_embedding_countable_complement]: direct
    formalisation of the special real-line assertion in Federer 2.2.9, p.
    65: Gamma is Borel, its complement in R is countable, and the sequence
    space is homeomorphic to Gamma. This is the interval-tree homeomorphism;
    no identification with the separately cited continued-fraction map is
    asserted. *)
Theorem real_sequence_borel_embedding_countable_complement (R : realType) :
  exists (G : set (real_line_metric R)) (g : positive_sequence_space R -> real_line_metric R),
    borel_set G /\ countable (~` G) /\ is_homeomorphism_onto G g.
Proof.
pose U := @RealIntervalTree.value R.
have hreal : is_real_interval_embedding_tree U := @RealIntervalTree.laws R.
have hU : is_open_embedding_tree U := real_interval_tree_open_laws hreal.
have hc := @real_line_metric_complete R.
pose g := @OpenEmbeddingMap.value R [the metricType R of real_line_metric R] hc U hU.
have hg : is_open_embedding_map U g := @OpenEmbeddingMap.laws R _ hc U hU.
exists (open_embedding_image U), g; split.
- exact: open_embedding_image_borel hU.
- split.
  + apply: (@open_embedding_image_countable_complement R
      [the metricType R of real_line_metric R] U hU).
    move=> s; exact: (@real_interval_tree_countable_loss R U hreal s).
  + constructor.
    * exact: (@open_embedding_map_injective R _ U hU g hg).
    * exact: (@open_embedding_map_image R _ U hU g hg).
    * exact: (@open_embedding_map_continuous R _ U hU g hg).
    * move=> O ho; exact: (@open_embedding_map_open R _ U hU g hg O ho).
Qed.
