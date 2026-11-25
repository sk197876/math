(** Federer (1969), 2.3.2, pp. 73–74: supporting graph-extensional
    measurability for partial numerical operations. Source context:
    PartialFunctionGraphEquivalence.v. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionGraphEquivalence
  MeasureAlmostUP MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [measurable_function_graph_equivalent]: supporting
    extensionality for the definition in Federer 2.3.2, p. 73.
    Equivalent graphs have identical measurable inverse images;
    no equality between the record proof fields is needed. *)
Lemma measurable_function_graph_equivalent (R : realType) (X : choiceType)
    (Y : topologicalType) (mu : set X -> \bar R) (f g : partial_function X Y) :
  (forall x y, partial_function_graph f x y <-> partial_function_graph g x y) ->
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g.
Proof.
move=> he hf; constructor.
- rewrite -(partial_function_equivalent_domains he); exact: measurable_function_domain hf.
- move=> U ho; rewrite -(partial_function_equivalent_preimages he).
  exact (@measurable_function_open_preimage R X Y mu f hf U ho).
Qed.
