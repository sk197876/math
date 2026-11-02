(** Federer (1969), 1.7.3, p. 29: supporting identification of norms on
    subspaces. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm ModuleQuotient SubspaceCarrier.
From Federer Require Import InnerProductRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [restricted_inner_normE]: Federer 1.7.3,
    p. 29, supporting fact: restriction to a subspace preserves
    the norm, since the diagonal inner product is unchanged. *)
Lemma restricted_inner_normE (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (W : subspace V) (x : subspace_space W) :
  inner_norm (@restricted_inner_productP R V B hB W) x =
  inner_norm hB (subspace_val x).
Proof.
apply: inner_norm_value; first exact: inner_norm_nonnegative.
by rewrite inner_norm_sqr.
Qed.
