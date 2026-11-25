(** Federer (1969), 2.2.11, p. 68: every complete, nonempty metric space
    without isolated points has a Suslin subset which is not Borel. The
    source sequence space is complete and separable; no separability
    hypothesis is imposed on the final target. Source context:
    CountableOpenBaseUP.v. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import SequenceSpace SequenceCompleteness SequenceSeparability CompleteMetricUP
  NoIsolatedPoints HomeomorphismOnto SequenceBorelEmbedding SuslinSetUP TopologicalBorel
  SequenceNonBorelSuslin NonBorelSuslinTransfer.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [complete_nonisolated_suslin_non_borel_exists]:
    direct final assertion in Federer 2.2.11, p. 68,
    retaining precisely completeness, nonemptiness and absence
    of isolated points in the ambient metric space. *)
Theorem complete_nonisolated_suslin_non_borel_exists (R : realType) (T : metricType R) :
  is_complete_metric_space T -> has_no_isolated_points T -> (@setT T) !=set0 ->
  exists S : set T, is_suslin_set R S /\ ~ borel_set S.
Proof.
move=> hT hno hn.
have [G [g [hG hg]]] := @complete_nonisolated_sequence_borel_embedding R T hT hno hn.
have [A [hA [_ hnot]]] := sequence_suslin_non_borel_exists R.
have hN : is_complete_metric_space [the metricType R of positive_sequence_space R].
  move=> F PF hc; exact: positive_sequence_cauchy_limit_exists PF hc.
exists (g @` A).
exact: (@injective_continuous_non_borel_suslin_image R
  [the metricType R of positive_sequence_space R] T g A hN (positive_sequence_separable R)
  (@metric_hausdorff R T) (homeomorphism_onto_continuous hg) (homeomorphism_onto_injective hg) hA hnot).
Qed.
