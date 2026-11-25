(** Cardinal assertions in the proof of Federer (1969), 2.2.4, p. 62
    Positive closed subsets are uncountable because their singletons are
    null, hence have continuum cardinality. Source context:
    SeparableMetricBaseConstruction.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic PositiveClosedSubsets
  CompleteMetricUP MetricSubsetBackground MetricClosedSubsetCompleteness
  MetricClosedSubsetSeparability PerfectKernelCardinality SequenceSpace
  SequenceContinuumCardinality CountableOpenBaseUP SeparableMetricBaseSealed
  CountableBaseCardinality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.
Local Open Scope ereal_scope.

(** Source for [positive_closed_family]: the family Gamma displayed in
    Federer 2.2.4, p. 62: closed subsets of A of strictly positive measure. *)
Definition positive_closed_family (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (A : set T) : set (set T) :=
  [set C | closed C /\ C `<=` A /\ 0 < mu C].

(** Source for [positive_closed_uncountable]: supporting first implication
    in Federer 2.2.4, p. 62 Positive measure and null singletons exclude
    countability, even without closedness of the set. *)
Lemma positive_closed_uncountable (R : realType) (T : choiceType)
    (mu : set T -> \bar R) (hm : is_measure mu) (C : set T) :
  0 < mu C -> (forall x, C x -> mu [set x] = 0) -> ~ countable C.
Proof.
move=> hp hz hc; have he := countable_null_singletons_null hm hc hz.
by rewrite he ltxx in hp.
Qed.

(** Source for [positive_closed_sequence_cardinality]: direct supporting
    cardinal equality for C in Federer 2.2.4, p. 62. *)
Theorem positive_closed_sequence_cardinality (R : realType) (T : metricType R)
    (mu : set T -> \bar R) (hm : is_measure mu) (C : set T) :
  is_complete_metric_space T ->
  (exists D : set T, countable D /\ dense D) -> closed C ->
  0 < mu C -> (forall x, C x -> mu [set x] = 0) ->
  C #= (@setT (positive_sequence_space R)).
Proof.
move=> hT hs hC hp hz.
have hunc : ~ countable C := positive_closed_uncountable hm hp hz.
have hn : C !=set0.
  apply: contrapT=> hnone; apply: hunc.
  have he : C = set0 by apply/seteqP; split=> // x hx; exfalso; apply: hnone; exists x.
  rewrite he; exact: countable0.
have huc : ~ countable (@setT (metric_subset C)).
  move=> hc; apply: hunc; by rewrite -(eq_countable (card_setT C)).
have he := @uncountable_complete_separable_sequence_cardinality R
  [the metricType R of metric_subset C]
  (@complete_closed_metric_subset R T C hT hC)
  (@nonempty_closed_metric_subset_separable R T C hs hC hn) huc.
exact: card_eq_trans (card_setT_sym C) he.
Qed.

(** Source for [positive_closed_family_cardinality_bound]: direct family
    bound in Federer 2.2.4, p. 62 Gamma is a subfamily of the closed sets,
    each encoded by a subset of a countable base. *)
Lemma positive_closed_family_cardinality_bound (R : realType) (T : metricType R)
    (mu : set T -> \bar R) (A : set T) :
  (exists D : set T, countable D /\ dense D) ->
  positive_closed_family mu A #<= (@setT (positive_sequence_space R)).
Proof.
move=> [D [hc hd]].
pose U := @SeparableMetricBase.value R T D hc hd.
have hU := @SeparableMetricBase.laws R T D hc hd.
have hsub : positive_closed_family mu A `<=` (@closed T) by move=> C [hC _].
have hb := card_le_trans (subset_card_le hsub) (countable_base_closed_cardinality_bound hU).
have he := positive_sequence_continuum_cardinality R.
by rewrite (card_le_eqr he).
Qed.
