(** Federer (1969), 1.7.3, p. 29: supporting specification for recursively
    decomposing an invariant subspace of a fixed ambient space. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ModuleQuotient MinimalInvariantUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_orthogonal_invariant_decomposition_of]: Federer
    1.7.3, p. 29, supporting relative form of the decomposition
    specification: its minimal summands lie in W and span exactly W. *)
Record is_orthogonal_invariant_decomposition_of (R : fieldType)
    (V : lmodType R) (B : V -> V -> R) (f : {linear V -> V})
    (W : subspace V) s (A : 'I_s -> subspace V) : Prop := {
  decomposition_of_contained : forall i x, A i x -> W x;
  decomposition_of_minimal : forall i, is_minimal_invariant_subspace f (A i);
  decomposition_of_orthogonal : forall i j, i != j ->
    forall x y, A i x -> A j y -> B x y = 0;
  decomposition_of_spans : forall x, W x ->
    exists a : 'I_s -> V, (forall i, A i (a i)) /\ x = \sum_i a i
}.
