(** Federer (1969), 2.4.10, p. 85, opening definition: f_A agrees with f on
    A and is zero on its complement. We give an abstract graph specification
    with a distinguished zero in an arbitrary target; real and extended-real
    instances support step functions and integrals respectively. *)
From mathcomp Require Import all_boot classical_sets.
From Federer Require Import PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_partial_function_zero_extension]: abstract
    graph specification of f_A in Federer 2.4.10,
    p. 85. Points in A outside the domain of f
    remain undefined; points outside A have the distinguished zero. *)
Definition is_partial_function_zero_extension (X Y : Type) (zero : Y)
    (A : set X) (f g : partial_function X Y) :=
  forall x y, partial_function_graph g x y <->
    (A x /\ partial_function_graph f x y) \/ (~ A x /\ y=zero).

(** Source for [partial_zero_extension_graph_unique]: supporting
    uniqueness of the graph defined in Federer 2.4.10,
    p. 85, including its exact partial domain. *)
Lemma partial_zero_extension_graph_unique (X Y : Type) (zero : Y)
    (A : set X) (f g h : partial_function X Y) :
  is_partial_function_zero_extension zero A f g ->
  is_partial_function_zero_extension zero A f h ->
  forall x y, partial_function_graph g x y <-> partial_function_graph h x y.
Proof. by move=> hg hh x y; rewrite (hg x y) (hh x y). Qed.
