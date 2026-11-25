(** Federer (1969), 4.1.1, p. 346: restrict
    the weak dual field to a compact support
    before using its local norm integral. This
    supporting measurable cutoff is 2.4.10, p. 85. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic PartialZeroExtension PartialZeroExtensionLaws
  MeasureUP MeasurableFunctionUP MeasurableZeroExtension MeasurableGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [measurable_total_cutoff]: setting a
    measurable total function to a fixed value
    off a measurable set preserves measurability,
    supporting Federer 4.1.1, p. 346. *)
Theorem measurable_total_cutoff (R:realType) (X:choiceType) (Y:topologicalType)
    (mu:set X->\bar R) (hm:is_measure mu) (S:set X) (f:X->Y) (z:Y):
  measure_measurable mu S ->is_measure_measurable_function mu (partial_function_total f) ->
  is_measure_measurable_function mu
    (partial_function_total (fun x=>if pselect (S x) then f x else z)).
Proof.
move=>hS hf.
have hZero:=measurable_zero_extension hm z hS hf.
apply:(@measurable_function_graph_equivalent R X Y mu
  (partial_function_zero_extension z S (partial_function_total f)) _ _ hZero)=>x y.
rewrite partial_function_zero_extension_graph.
change ((S x /\ f x=y) \/ (~S x /\ y=z) <-> (if pselect (S x) then f x else z)=y).
case:(pselect (S x))=>hx.
- split.
  + move=>[[hs he]|[hn he]]; first exact he; exact:False_ind _ (hn hx).
  + move=>he; left; by split.
- split.
  + move=>[[hs he]|[hn he]]; first exact:False_ind _ (hx hs); exact:esym he.
  + move=>he; right; split=>//; exact:esym he.
Qed.
