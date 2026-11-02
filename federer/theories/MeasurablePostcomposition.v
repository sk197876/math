(** Federer (1969), 2.3.2(4), p. 73: Borel functions preserve measurability
    under postcomposition. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionPostcomposition
  MeasureUP MeasureAlmostUP MeasurableFunctionUP MeasurableFunctionBorel
  BorelFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [measurable_function_borel_postcomposition]: direct Federer
    2.3.2(4), p. 73 The input function may have a partial domain. *)
Theorem measurable_function_borel_postcomposition (R : realType)
    (X : choiceType) (Y Z : topologicalType) (mu : set X -> \bar R)
    (hm : is_measure mu) (f : partial_function X Y) (g : Y -> Z) :
  is_measure_measurable_function mu f -> is_borel_function g ->
  is_measure_measurable_function mu (partial_function_postcompose f g).
Proof.
move=> hf hg; constructor.
- rewrite /measure_almost_everywhere partial_function_postcompose_domain.
  exact: measurable_function_domain hf.
- move=> U ho; rewrite partial_function_postcompose_preimage.
  exact (@measurable_function_borel_preimage R X Y mu hm f hf _ (hg U ho)).
Qed.
