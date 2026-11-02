(** Federer (1969), 1.7.3, p. 29: supporting homogeneous bound inside the
    subspace orthogonal to preceding axes. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm ModuleQuotient
  SubspaceCarrier TensorUP InnerProductRestriction InnerRestrictedNorm
  SemidefiniteRestriction RayleighBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [quadratic_unit_bound_in_subspace]: Federer 1.7.3,
    p. 29, supporting homogeneous extension of a maximum over the
    unit sphere in the current constraint subspace. *)
Theorem quadratic_unit_bound_in_subspace (R : rcfType) (V : lmodType R)
    (B S : V -> V -> R) (hB : is_inner_product B)
    (hS : @bilinear R V V R^o S) (W : subspace V) lambda :
  (forall x, W x -> inner_norm hB x = 1 -> S x x <= lambda) ->
  forall x, W x -> S x x <= lambda * B x x.
Proof.
move=> hm x hx.
have hunit (y : subspace_space W) :
    inner_norm (@restricted_inner_productP R V B hB W) y = 1 ->
    @restricted_inner_product R V S W y y <= lambda.
  rewrite restricted_inner_normE => hy; apply: hm => //; exact: subspace_valP.
exact (@quadratic_unit_bound R (subspace_space W)
  (@restricted_inner_product R V B W) (@restricted_inner_product R V S W)
  (@restricted_inner_productP R V B hB W) (@restricted_bilinearP R V S hS W)
  lambda hunit (subspace_lift hx)).
Qed.
