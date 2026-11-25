(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import InteriorDecomposition.
From Federer Require Import SubspaceCarrier AssociatedSubspace
  AssociatedFiniteFamily BoundedIndependentBasis FiniteBasisComparison.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1, k=dim T<=m: this is a statement about T itself,
    even when V is infinite dimensional. A finite basis is constructed,
    and the dimension is independent of that choice. *)
Section Dimension.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable m : nat.
Variable xi : exterior_power V m.
Hypothesis hxi : xi != 0.
Local Notation T := (FedererSimple.T xi).
Local Notation U := (GRing.Lmodule.clone K (subspace_space T) _).
(** Source for [associated_independent_bound]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Lemma associated_independent_bound k (e : 'I_k -> U) :
  finite_independent e -> (k <= m)%N.
Proof.
move=> he.
have hv : finite_independent (fun i => subspace_inclusion T (e i)).
  exact: finite_independent_map (@subspace_val_injective K V T) he.
have ht i : T (subspace_inclusion T (e i)) := subspace_valP (e i).
exact (proj1 (@associated_finite_family K h2 V m k xi _ hv ht hxi)).
Qed.
(** Source for [associated_basis_exists]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Theorem associated_basis_exists : exists k (e : 'I_k -> U),
  is_basis e /\ (k <= m)%N.
Proof. exact: bounded_independent_basis associated_independent_bound. Qed.
(** Source for [associated_k]: Federer (1969), 1.6.1, p. 23, dimension
    bound, factorisation assertion, and finite-dimensional reduction. In
    words: For a nonzero m-vector the associated space has dimension k<=m;
    the product of any basis of that space factors from the vector, leaving
    degree m-k. Definition or construction used to formalise this passage. *)
Definition associated_k : nat := proj1_sig
  (constructive_indefinite_description associated_basis_exists).
(** Source for [associated_kP]: Federer (1969), 1.6.1, p. 23, dimension
    bound, factorisation assertion, and finite-dimensional reduction. In
    words: For a nonzero m-vector the associated space has dimension k<=m;
    the product of any basis of that space factors from the vector, leaving
    degree m-k. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma associated_kP : exists e : 'I_associated_k -> U,
  is_basis e /\ (associated_k <= m)%N.
Proof. exact (proj2_sig (constructive_indefinite_description associated_basis_exists)). Qed.
(** Source for [associated_e]: Federer (1969), 1.6.1, p. 23, dimension
    bound, factorisation assertion, and finite-dimensional reduction. In
    words: For a nonzero m-vector the associated space has dimension k<=m;
    the product of any basis of that space factors from the vector, leaving
    degree m-k. Definition or construction used to formalise this passage. *)
Definition associated_e : 'I_associated_k -> U := proj1_sig
  (constructive_indefinite_description associated_kP).
(** Source for [associated_e_basis]: Federer (1969), 1.6.1, p. 23, dimension
    bound, factorisation assertion, and finite-dimensional reduction. In
    words: For a nonzero m-vector the associated space has dimension k<=m;
    the product of any basis of that space factors from the vector, leaving
    degree m-k. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma associated_e_basis : is_basis associated_e.
Proof. exact (proj1 (proj2_sig (constructive_indefinite_description associated_kP))). Qed.
(** Source for [associated_space]: Federer (1969), 1.6.1, p. 23, dimension
    bound, factorisation assertion, and finite-dimensional reduction. In
    words: For a nonzero m-vector the associated space has dimension k<=m;
    the product of any basis of that space factors from the vector, leaving
    degree m-k. Definition or construction used to formalise this passage. *)
Definition associated_space : vectType K := finite_basis_vect associated_e_basis.
(** Source for [associated_dimension]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Theorem associated_dimension : (dim associated_space <= m)%N.
Proof.
rewrite /associated_space finite_basis_dimension card_ord.
exact (proj2 (proj2_sig (constructive_indefinite_description associated_kP))).
Qed.
(** Source for [associated_basis_dimension]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Theorem associated_basis_dimension k (e : 'I_k -> U) :
  is_basis e -> dim associated_space = k.
Proof.
move=> he; rewrite /associated_space finite_basis_dimension card_ord.
exact: finite_basis_size associated_e_basis he.
Qed.

(** Federer 1.6.1: the factorisation holds for any prescribed basis
    e_1,...,e_k of T, not merely the basis selected above. *)
(** Source for [associated_basis_factorisation]: Federer (1969), 1.6.1, p.
    23, dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Theorem associated_basis_factorisation k (e : 'I_k -> U) (he : is_basis e) :
  (k <= m)%N /\ exists xi_prime : exterior_power V (m-k),
    component_val xi = wedge
      (component_val (e_lambda (fun i => subspace_val (e i)) (ord_tuple k)))
      (component_val xi_prime).
Proof.
have hi := finite_basis_independent he.
have hv : finite_independent (fun i => subspace_inclusion T (e i)).
  exact: finite_independent_map (@subspace_val_injective K V T) hi.
have ht i : T (subspace_inclusion T (e i)) := subspace_valP (e i).
exact (@associated_finite_family K h2 V m k xi _ hv ht hxi).
Qed.
End Dimension.
