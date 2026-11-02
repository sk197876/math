(** Federer (1969), 1.7.3, p. 29: public existence theorem for the minimal
    orthogonal invariant decomposition. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ModuleQuotient LinearBasis InnerProductUP
  SymmetricEndomorphisms MinimalInvariantUP OrthogonalDecompositionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [orthogonal_invariant_decomposition_exists]:
    Federer 1.7.3, p. 29, the finite orthogonal decomposition
    into minimal nonzero invariant subspaces, obtained from its
    sealed existence interface. *)
Theorem orthogonal_invariant_decomposition_exists (R : rcfType)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (b : 'I_n -> V) (hb : is_basis b) (f : {linear V -> V}) :
    is_symmetric_endomorphism B f \/ is_skewsymmetric_endomorphism B f ->
    exists s (A : 'I_s -> subspace V),
      is_orthogonal_invariant_decomposition B f A.
Proof. exact: (@OrthogonalDecomposition.exists_decomposition R V B hB n b hb f). Qed.
