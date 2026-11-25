(** Public pointwise sum for Federer (1969), 2.4.8, p. 84, using only the
    sealed graph specification. Source context: PartialNumericalSumUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialNumericalSumUP PartialNumericalSumSealed NumericalSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_function_numerical_sum]: public
    pointwise sum in Federer 2.4.8, p. 84. *)
Definition partial_function_numerical_sum (R : realType) (X : Type) (J : choiceType)
    (D : set J) (f : J -> partial_function X (extended_real_line R)) :=
  PartialNumericalSum.value D f.

(** Source for [partial_function_numerical_sum_laws]: public
    graph specification of the sum in Federer 2.4.8, p. 84. *)
Lemma partial_function_numerical_sum_laws (R : realType) (X : Type) (J : choiceType)
    (D : set J) (f : J -> partial_function X (extended_real_line R)) :
  is_partial_function_numerical_sum D f (partial_function_numerical_sum D f).
Proof. exact: PartialNumericalSum.laws. Qed.

(** Source for [partial_function_numerical_sum_graph]: usable
    graph equation for the pointwise sum in Federer 2.4.8,
    p. 84, preserving undefined numerical sums and partial domains. *)
Lemma partial_function_numerical_sum_graph (R : realType) (X : Type) (J : choiceType)
    (D : set J) (f : J -> partial_function X (extended_real_line R)) x z :
  partial_function_graph (partial_function_numerical_sum D f) x z <-> exists u : J -> \bar R,
    (forall j, D j -> partial_function_graph (f j) x (u j)) /\ numerical_sum D u = Some z.
Proof. exact: partial_function_numerical_sum_laws. Qed.
