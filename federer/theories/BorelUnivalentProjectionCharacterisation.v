(** Federer (1969), 2.2.10, p. 68, final paragraph: in a complete separable
    metric space the Borel sets are precisely the one-to-one projection
    images of closed subsets of X times N. Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot classical_sets cardinality reals topology.
From Federer Require Import SequenceSpace SequenceCompleteness SequenceSeparability
  CompleteMetricUP SuslinSetUP BorelClosedProjection TopologicalBorel TopologicalProductMaps
  MetricProductBackground MetricProductCompleteness MetricProductSeparability InjectiveClosedImageBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_iff_univalent_closed_projection]: direct one-to-one
    projection characterization in Federer 2.2.10, p. 68. The forward
    implication needs only a metric space; completeness and separability are
    used in the reverse implication for the closed subset of X times N. *)
Theorem borel_iff_univalent_closed_projection (R : realType) (T : metricType R)
    (S : set T) : is_complete_metric_space T ->
  (exists H : set T, countable H /\ dense H) ->
  (borel_set S <-> has_univalent_closed_projection R S).
Proof.
move=> hT hsep; split; first exact: metric_borel_univalent_closed_projection.
move=> [C hC].
pose P := [the metricType R of metric_product T (positive_sequence_space R)].
have hN : is_complete_metric_space [the metricType R of positive_sequence_space R].
  move=> F PF hc; exact: positive_sequence_cauchy_limit_exists PF hc.
have hP : is_complete_metric_space P := complete_metric_product hT hN.
have hsP : exists H : set P, countable H /\ dense H.
  exact: separable_metric_product hsep (positive_sequence_separable R).
rewrite -(@univalent_projection_image R T S C hC).
exact: (@injective_closed_image_borel R P T (@fst T (positive_sequence_space R)) C
  hP hsP (@metric_hausdorff R T) (@first_projection_continuous T (positive_sequence_space R))
  (@univalent_projection_closed R T S C hC)
  (@univalent_projection_injective R T S C hC)).
Qed.
