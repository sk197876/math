(** Federer (1969), 2.2.10, p. 65: every nonempty Suslin subset of a
    complete separable metric space is a continuous image of N. The proof
    follows the printed reduction: a closed witness C in X times N is
    complete and separable; apply 2.2.8 to C, then project. Source context:
    SuslinSetUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals topology.
From Federer Require Import SequenceSpace SequenceCompleteness SequenceSeparability
  CompleteMetricUP SuslinSetUP SequenceParametrisation TopologicalProductMaps
  MetricProductBackground MetricProductCompleteness MetricProductSeparability
  MetricSubsetBackground MetricClosedSubsetCompleteness MetricClosedSubsetSeparability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [nonempty_suslin_sequence_parametrisation]: direct
    continuous-parametrisation assertion in Federer 2.2.10,
    p. 65, with all printed hypotheses retained. The map's
    image is exactly S. All completeness, separability and closed-
    witness steps are supplied by locally proved results. *)
Theorem nonempty_suslin_sequence_parametrisation (R : realType) (T : metricType R)
    (S : set T) :
  is_complete_metric_space T ->
  (exists D : set T, countable D /\ dense D) ->
  is_suslin_set R S -> S !=set0 ->
  exists h : positive_sequence_space R -> T, continuous h /\ h @` setT = S.
Proof.
move=> hT hsep [C [hC hCS]] hn.
pose P := [the metricType R of metric_product T (positive_sequence_space R)].
have hN : is_complete_metric_space [the metricType R of positive_sequence_space R].
  move=> F PF hc; exact: positive_sequence_cauchy_limit_exists PF hc.
have hP : is_complete_metric_space P := complete_metric_product hT hN.
have hsP : exists D : set P, countable D /\ dense D.
  exact: separable_metric_product hsep (positive_sequence_separable R).
have hnC : (C : set P) !=set0.
  have [x hx] := hn; rewrite -hCS in hx; have [p hp _] := hx; by exists p.
pose V := [the metricType R of @metric_subset R P C].
have hV : is_complete_metric_space V := @complete_closed_metric_subset R P C hP hC.
have hsV : exists D : set V, countable D /\ dense D.
  exact: (@nonempty_closed_metric_subset_separable R P C hsP hC hnC).
have hnV : (@setT V) !=set0.
  have [p hp] := hnC; exists (@exist P (fun y => y \in C) p (mem_set hp)); exact Logic.I.
have [g [honto [_ hg]]] := @complete_separable_sequence_parametrisation R V hV hsV hnV.
pose h n : T := (val (g n)).1.
exists h; split.
- move=> n.
  have hi := @metric_subset_inclusion_continuous R P C (g n).
  have hc := continuous_comp (hg n) hi.
  exact: continuous_comp hc (@first_projection_continuous T (positive_sequence_space R) (val (g n))).
- rewrite -hCS; apply/seteqP; split.
  + move=> x [n _ <-]; exists (val (g n))=> //; exact: set_valP.
  + move=> x [p hp <-].
    pose a : V := @exist P (fun y => y \in C) p (mem_set hp).
    have [n hn'] := honto a; exists n=> //.
    by rewrite /h hn'.
Qed.
