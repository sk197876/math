(** Federer (1969), 1.7.3, p. 29: minimal nonzero invariant summands. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ModuleQuotient SymmetricEndomorphisms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_minimal_invariant_subspace]: Federer 1.7.3,
    p. 29, the nonzero invariant summands have no proper nonzero
    invariant subspace. This specifies minimality by inclusion. *)
Record is_minimal_invariant_subspace (R : fieldType) (V : lmodType R)
    (f : {linear V -> V}) (W : subspace V) : Prop := {
  minimal_invariant_nonzero : exists x, W x /\ x != 0;
  minimal_invariant_stable : invariant_subspace f W;
  minimal_invariant_minimal : forall Z : subspace V,
    (forall x, Z x -> W x) -> (exists x, Z x /\ x != 0) ->
    invariant_subspace f Z -> forall x, W x -> Z x
}.

(** Source for [is_orthogonal_invariant_decomposition]: Federer
    1.7.3, p. 29, decomposition into finitely many mutually
    perpendicular minimal nonzero invariant subspaces. The spanning
    and orthogonality laws include the empty decomposition of zero. *)
Record is_orthogonal_invariant_decomposition (R : fieldType)
    (V : lmodType R) (B : V -> V -> R) (f : {linear V -> V})
    s (W : 'I_s -> subspace V) : Prop := {
  invariant_decomposition_minimal : forall i, is_minimal_invariant_subspace f (W i);
  invariant_decomposition_orthogonal : forall i j, i != j ->
    forall x y, W i x -> W j y -> B x y = 0;
  invariant_decomposition_spans : forall x,
    exists w : 'I_s -> V, (forall i, W i (w i)) /\ x = \sum_i w i
}.
