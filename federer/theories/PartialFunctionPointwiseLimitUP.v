(** Federer (1969), 2.3.9, pp. 79–80: the function h assigns the limit at
    each point where the sequence is defined and converges. This graph
    specification retains partial domains. *)
From mathcomp Require Import all_boot classical_sets topology.
From Federer Require Import PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_partial_function_pointwise_limit]: abstract
    specification of h in Federer 2.3.9, pp. 79–80.
    Its domain is precisely the common-domain convergence locus. *)
Definition is_partial_function_pointwise_limit (X : Type) (Y : topologicalType)
    (f : nat -> partial_function X Y) (h : partial_function X Y) :=
  forall x y, partial_function_graph h x y <-> exists u : nat -> Y,
    (forall n, partial_function_graph (f n) x (u n)) /\ u @ \oo --> y.
