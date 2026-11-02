(** Federer (1969), 2.3.7, pp. 77–78: common defined values for uniform
    convergence. Source context: UniformPartialConvergenceUP.v. *)
From mathcomp Require Import all_boot classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureFiniteClosure MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_sequence_common_domain]: Supporting Federer 2.3.7,
    pp. 77–78. *)
Definition partial_sequence_common_domain (X Y : Type)
    (f : nat -> partial_function X Y) (g : partial_function X Y) :=
  partial_function_domain g `&` (\bigcap_n partial_function_domain (f n)).

(** Source for [partial_sequence_common_domain_conull]: supporting countable
    intersection of conull domains for Federer 2.3.7, p. 78 *)
Lemma partial_sequence_common_domain_conull (R : realType) (X : choiceType)
    (Y : topologicalType) (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X Y) (g : partial_function X Y) :
  (forall n, is_measure_measurable_function mu (f n)) -> is_measure_measurable_function mu g ->
  measure_almost_everywhere mu (partial_sequence_common_domain f g).
Proof.
move=> hf hg; apply: (@measure_almost_everywhere_and R X mu hm).
- exact: measurable_function_domain hg.
- apply: (@measure_almost_everywhere_countable R X nat mu hm setT _ (countableP _)).
  move=> n _; exact: measurable_function_domain (hf n).
Qed.

(** Source for [partial_sequence_common_domain_measurable]: Supporting
    Federer 2.3.7, p. 78. *)
Lemma partial_sequence_common_domain_measurable (R : realType) (X : choiceType)
    (Y : topologicalType) (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X Y) (g : partial_function X Y) :
  (forall n, is_measure_measurable_function mu (f n)) -> is_measure_measurable_function mu g ->
  measure_measurable mu (partial_sequence_common_domain f g).
Proof.
move=> hf hg.
have hn := @partial_sequence_common_domain_conull R X Y mu hm f g hf hg.
have hc := @measure_null_measurable R X mu hm (~` partial_sequence_common_domain f g) hn.
have hh := measure_measurable_complement hc; by rewrite setCK in hh.
Qed.
