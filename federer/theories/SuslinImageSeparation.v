(** Federer (1969), 2.2.10, p. 67: the separation theorem extends from
    closed sets to Suslin sets by using their closed witnesses in X times N.
    Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot classical_sets cardinality reals topology.
From Federer Require Import SequenceSpace SequenceCompleteness SequenceSeparability
  CompleteMetricUP SuslinSetUP TopologicalProductMaps MetricProductBackground
  MetricProductCompleteness MetricProductSeparability BorelSeparation ClosedImageBorelSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [disjoint_suslin_images_borel_separated]: supporting
    extension used for the disjoint Suslin-image assertion in Federer
    2.2.10, p. 67. Apply (1) to the two closed witnesses in X times N and
    the continuous map f composed with projection. *)
Theorem disjoint_suslin_images_borel_separated (R : realType) (T : metricType R)
    (Y : topologicalType) (f : T -> Y) (A B : set T) :
  is_complete_metric_space T ->
  (exists H : set T, countable H /\ dense H) -> hausdorff_space Y -> continuous f ->
  is_suslin_set R A -> is_suslin_set R B ->
  (f @` A) `&` (f @` B) = set0 -> borel_separated (f @` A) (f @` B).
Proof.
move=> hT hsep hY hf [C [hC hCA]] [D [hD hDB]] hdis.
pose P := [the metricType R of metric_product T (positive_sequence_space R)].
have hN : is_complete_metric_space [the metricType R of positive_sequence_space R].
  move=> F PF hc; exact: positive_sequence_cauchy_limit_exists PF hc.
have hP : is_complete_metric_space P := complete_metric_product hT hN.
have hsP : exists H : set P, countable H /\ dense H.
  exact: separable_metric_product hsep (positive_sequence_separable R).
pose g (p : P) := f p.1.
have hg : continuous g.
  move=> p; exact: continuous_comp (@first_projection_continuous T (positive_sequence_space R) p) (hf p.1).
have heC : g @` C = f @` A.
  rewrite -hCA; exact: esym (image_comp (@fst T (positive_sequence_space R)) f C).
have heD : g @` D = f @` B.
  rewrite -hDB; exact: esym (image_comp (@fst T (positive_sequence_space R)) f D).
have hd0 : (g @` C) `&` (g @` D) = set0 by rewrite heC heD.
have hs := @disjoint_closed_images_borel_separated R P Y g C D hP hsP hY hg hC hD hd0.
by rewrite heC heD in hs.
Qed.
