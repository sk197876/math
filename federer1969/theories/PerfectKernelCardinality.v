(** Federer (1969), 2.2.4, p. 62: every uncountable complete separable
    metric space has continuum cardinality. We retain that proof and use
    only abstract countable-base, completeness, parametrisation and
    embedding interfaces. Source context: SeparableMetricBaseConstruction.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals topology.
From Federer Require Import SequenceSpace CompleteMetricUP SequenceParametrisation
  SequenceBorelEmbedding HomeomorphismOnto CardinalInjection
  CountableOpenBaseUP SeparableMetricBaseSealed CountableNeighborhoodLocus
  CondensationKernel MetricSubsetBackground MetricClosedSubsetCompleteness
  SequenceContinuumCardinality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

(** Source for [uncountable_complete_separable_sequence_cardinality]:
    Supporting Federer 2.2.4, p. 62.The sequence space embeds in the closed
    condensation kernel, while 2.2.8 gives a surjection onto the original
    space. No continuum hypothesis or regularity of the continuum is
    assumed. *)
Theorem uncountable_complete_separable_sequence_cardinality
    (R : realType) (T : metricType R) :
  is_complete_metric_space T ->
  (exists D : set T, countable D /\ dense D) ->
  ~ countable (@setT T) -> (@setT T) #= (@setT (positive_sequence_space R)).
Proof.
move=> hT [D [hc hd]] hunc.
pose U := @SeparableMetricBase.value R T D hc hd.
have hU : is_countable_open_base U := @SeparableMetricBase.laws R T D hc hd.
pose K := ~` @countable_neighborhood_locus T.
have hK : closed K := @countable_neighborhood_complement_closed T.
have hKn : K !=set0 := countable_neighborhood_complement_nonempty hU hunc.
have hn : (@setT T) !=set0 by have [x hx] := hKn; exists x.
have hsubn : (@setT (metric_subset K)) !=set0.
  have [x hx] := hKn; exists (@exist T (fun y => y \in K) x (mem_set hx)); exact Logic.I.
have hsubc := @complete_closed_metric_subset R T K hT hK.
have hsubno := @condensation_kernel_no_isolated_points R T U hU.
have [G [g [hG hg]]] := @complete_nonisolated_sequence_borel_embedding R
  [the metricType R of metric_subset K] hsubc hsubno hsubn.
apply/card_eqPle; split.
- have hsep : exists D : set T, countable D /\ dense D by exists D.
  have [f [hf _]] := complete_separable_sequence_parametrisation hT hsep hn.
  have he : f @` setT = setT.
    apply/seteqP; split=> // x _; have [n <-] := hf x; by exists n.
  have hh := @card_image_le _ _ f setT; by rewrite he in hh.
- apply: (@cardinal_bound_of_injection _ _ setT setT (fun n => (val (g n) : T))).
  + by move=> n _.
  + move=> n m _ _ he; apply: (@homeomorphism_onto_injective _ _ G g hg n m).
    exact: val_inj he.
Qed.

(** Source for [uncountable_complete_separable_continuum_cardinality]: the
    supporting cardinal equality stated in Federer 2.2.4, p. 62. Continuum
    is represented by the full natural power set. *)
Theorem uncountable_complete_separable_continuum_cardinality
    (R : realType) (T : metricType R) :
  is_complete_metric_space T ->
  (exists D : set T, countable D /\ dense D) ->
  ~ countable (@setT T) -> (@setT T) #= (@setT (set nat)).
Proof.
move=> hT hs hu; apply: card_eq_trans (uncountable_complete_separable_sequence_cardinality hT hs hu) _.
exact: positive_sequence_continuum_cardinality.
Qed.
