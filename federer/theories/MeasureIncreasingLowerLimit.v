(** Federer (1969), 2.4.7, p. 84: common almost- everywhere monotonicity
    gives an almost-everywhere increasing limit and comparison with every
    term. The common good set is obtained by the project's countable
    null-exception rule. Source context: ExtendedIncreasingLowerLimit.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionLimitExtremaUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic PartialExtendedOrderLoci PartialIncreasingLowerLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_increasing_lower_limit_laws]: supporting pointwise
    convergence and comparison in Federer 2.4.7, p. 84. *)
Lemma measure_increasing_lower_limit_laws (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) :
  is_partial_function_lower_limit f g ->
  (forall n, measure_almost_everywhere mu (partial_extended_le_locus (f n) (f n.+1))) ->
  measure_almost_everywhere mu (partial_extended_increasing_limit_locus f g) /\
  forall n, measure_almost_everywhere mu (partial_extended_le_locus (f n) g).
Proof.
move=> hg hf.
have he := @measure_almost_everywhere_countable R X [the choiceType of (nat : Type)] mu hm setT
  (fun n => partial_extended_le_locus (f n) (f n.+1)) (countableP _) (fun n _ => hf n).
split.
- apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he)=> x hx.
  exact (@partial_increasing_sequence_lower_limit R X f g x hg (fun n => hx n Logic.I)).1.
- move=> n; apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he)=> x hx.
  exact ((@partial_increasing_sequence_lower_limit R X f g x hg (fun n => hx n Logic.I)).2 n).
Qed.
