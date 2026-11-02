(** Federer (1969), 1.7.3, p. 29: specification of the successive
    maximisation used to choose principal axes. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm OrthonormalFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_maximal_orthonormal_family]: Federer 1.7.3,
    p. 29, inductive choice: each e_j maximises S(x,x) among unit
    vectors orthogonal to all its predecessors. This specification
    records the entire successive-maximisation property. *)
Record is_maximal_orthonormal_family (R : rcfType) (V : lmodType R)
    (B S : V -> V -> R) (hB : is_inner_product B) k (e : 'I_k -> V) : Prop := {
  maximal_family_orthonormal : orthonormal_family B e;
  maximal_family_value : forall (i : 'I_k) x, inner_norm hB x = 1 ->
    (forall j : 'I_k, (j < i)%N -> B x (e j) = 0) ->
    S x x <= S (e i) (e i)
}.
