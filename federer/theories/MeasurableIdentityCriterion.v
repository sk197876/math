(** Federer (1969), 2.3.2, p. 75, paragraph preceding (9): the identity is
    measurable exactly when every open set is measurable. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [measurable_identity_iff_open_sets]: direct identity
    observation in Federer 2.3.2, p. 75, before (9). *)
Theorem measurable_identity_iff_open_sets (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  is_measure_measurable_function mu (partial_function_total (fun x : X => x)) <->
  forall U, open U -> measure_measurable mu U.
Proof.
split.
- move=> hf U hU; have h := @measurable_function_open_preimage R X X mu _ hf U hU.
  by rewrite partial_function_total_preimage in h.
- move=> ho; constructor.
  + rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hm.
  + move=> U hU; rewrite partial_function_total_preimage; exact: ho U hU.
Qed.
