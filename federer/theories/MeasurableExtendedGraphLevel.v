(** Federer (1969), 2.9.11, p. 158: choose a phi hull of A before comparing
    its density with a characteristic function. Here the original class M
    permits a Borel hull, obtained from finite local hulls on the bounded
    Borel partition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureUP MeasurableFunctionUP
  MeasurableFunctionBorel ExtendedArithmeticDomains.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_extended_graph_level]: supporting measurability
    of the P and Q levels in Federer 2.9.11, p. 158 Singletons are Borel in
    the extended real line, and the preimage includes only defined
    partial-function values. *)
Lemma measurable_extended_graph_level (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (f : partial_function X (extended_real_line R)) a :
  is_measure phi -> is_measure_measurable_function phi f ->
  measure_measurable phi [set x | partial_function_graph f x a].
Proof.
move=> hm hf.
have h := @measurable_function_borel_preimage R X (extended_real_line R) phi hm f hf
  [set y | y==a] (@extended_order_singleton_borel R a).
have he : partial_function_preimage f [set y | y==a]=[set x | partial_function_graph f x a].
  apply/seteqP; split=> x.
  - by move=> [y [hy /eqP <-]].
  - move=> hx; exists a; split=> //; exact: eqxx.
by rewrite he in h.
Qed.
