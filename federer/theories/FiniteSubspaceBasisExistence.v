(** Federer (1969), 3.2.28(1), printed p. 263: Y_m is a
    finite-dimensional subspace of Hom(R^m,R^m). The existence
    of a finite basis of any finite-dimensional ambient subspace
    is separated from the ensuing exact dimension calculation. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ModuleQuotient SubspaceCarrier LinearBasis
  FiniteIndependence FiniteBasisComparison FiniteDimension IndependentMap
  BoundedIndependentBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_subspace_basis_exists]: supporting finite
    dimensionality of Y_m in Federer 3.2.28(1), p. 263,
    by the basis-size argument of 1.6.1, p. 23. No
    basis is selected globally and no dimension equality is assumed. *)
Theorem finite_subspace_basis_exists (K:fieldType) (V:lmodType K)
    n (b:'I_n->V) (hb:is_basis b) (S:subspace V):
  exists q (e:'I_q->subspace_space S), is_basis e /\ (q<=n)%N.
Proof.
apply:bounded_independent_basis=>q e he.
have hi:=@finite_independent_map K (Finite.clone 'I_q _)
  (subspace_space S) V (@subspace_inclusion K V S) e
  (@subspace_val_injective K V S) he.
have hq:=@finite_independent_dimension K (finite_basis_vect hb) q
  (fun i=>subspace_val (e i)) hi.
by rewrite finite_basis_dimension card_ord in hq.
Qed.
