(** Federer (1969), 2.2.10, p. 67, final sentence: the injective-image
    theorem also holds for Borel domains. Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot classical_sets cardinality reals topology.
From Federer Require Import SequenceSpace SequenceCompleteness SequenceSeparability
  CompleteMetricUP SuslinSetUP BorelClosedProjection TopologicalBorel TopologicalProductMaps
  MetricProductBackground MetricProductCompleteness MetricProductSeparability InjectiveClosedImageBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [injective_borel_image_borel]: direct Borel-domain extension
    in Federer 2.2.10, p. 67. The map is continuous on the complete
    separable metric space and is required to be injective only on A. The
    target is merely Hausdorff. *)
Theorem injective_borel_image_borel (R : realType) (T : metricType R)
    (Y : topologicalType) (f : T -> Y) (A : set T) :
  is_complete_metric_space T ->
  (exists H : set T, countable H /\ dense H) -> hausdorff_space Y -> continuous f ->
  borel_set A -> (forall x y, A x -> A y -> f x = f y -> x = y) -> borel_set (f @` A).
Proof.
move=> hT hsep hY hf hA hinj.
have [C hC] := @metric_borel_univalent_closed_projection R T A hA.
pose P := [the metricType R of metric_product T (positive_sequence_space R)].
have hN : is_complete_metric_space [the metricType R of positive_sequence_space R].
  move=> F PF hc; exact: positive_sequence_cauchy_limit_exists PF hc.
have hP : is_complete_metric_space P := complete_metric_product hT hN.
have hsP : exists H : set P, countable H /\ dense H.
  exact: separable_metric_product hsep (positive_sequence_separable R).
pose g (p : P) := f p.1.
have hg : continuous g.
  move=> p; exact: continuous_comp (@first_projection_continuous T (positive_sequence_space R) p) (hf p.1).
have hCA := @univalent_projection_image R T A C hC.
have heC : g @` C = f @` A.
  rewrite -hCA; exact: esym (image_comp (@fst T (positive_sequence_space R)) f C).
have hgi : forall p q : P, C p -> C q -> g p = g q -> p = q.
  move=> p q hp hq he; apply: (@univalent_projection_injective R T A C hC p q hp hq).
  apply: hinj he.
  - rewrite -hCA; by exists p.
  - rewrite -hCA; by exists q.
rewrite -heC; exact: (@injective_closed_image_borel R P Y g C hP hsP hY hg
  (@univalent_projection_closed R T A C hC) hgi).
Qed.
