(** Federer (1969), 1.7.3, p. 29: sealed existence of the orthogonal
    invariant decomposition. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ModuleQuotient LinearBasis InnerProductUP
  SymmetricEndomorphisms MinimalInvariantUP OrthogonalDecompositionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type OrthogonalDecompositionSig.
(** Source for [exists_decomposition]: Federer 1.7.3, p. 29,
    existence specified only through minimality, invariance,
    orthogonality and spanning, independently of the construction. *)
Parameter exists_decomposition : forall (R : rcfType) (V : lmodType R)
    (B : V -> V -> R), is_inner_product B ->
    forall n (b : 'I_n -> V), is_basis b ->
    forall f : {linear V -> V},
    is_symmetric_endomorphism B f \/ is_skewsymmetric_endomorphism B f ->
    exists s (A : 'I_s -> subspace V),
      is_orthogonal_invariant_decomposition B f A.
End OrthogonalDecompositionSig.

Module OrthogonalDecomposition : OrthogonalDecompositionSig.
(** Source for [exists_decomposition]: Federer 1.7.3, p. 29,
    the proved existence witness supplies the sealed specification. *)
Theorem exists_decomposition (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (b : 'I_n -> V) (hb : is_basis b) (f : {linear V -> V})
    (hf : is_symmetric_endomorphism B f \/ is_skewsymmetric_endomorphism B f) :
    exists s (A : 'I_s -> subspace V),
      is_orthogonal_invariant_decomposition B f A.
Proof. exact: (@orthogonal_decomposition_witness R V B hB n b hb f hf). Qed.
End OrthogonalDecomposition.
