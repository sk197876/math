(** General topology supporting Federer (1969), 2.7.16, examples (2) and
    (3), printed pp. 136–138: a finite dimensional inner product space has a
    countable base of open sets. Federer uses this without comment when he
    regards a Haar measure of the additive group of Hom(V, V), or of a
    subspace X of it, as a measure over the open set G of linear
    automorphisms; it is the hypothesis of 2.5.14, p. 107, under which the
    K(G) regular measure associated with an integral is a Radon measure. An
    orthonormal base e_1, ..., e_N (Gram–Schmidt, 1.7.1, p. 28) yields the
    isometry Phi(x) = sum_i x_i e_i of R^N onto the space
    (FiniteHaarLinear.v), and the inverse images under Phi^{-1} of a
    countable base of R^N form a countable base. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerMetric LinearBasis OrthonormalFamilies OrthonormalisationUP GramSchmidt
  HomeomorphismUP CountableOpenBaseUP EuclideanLebesgueHaar MeasureCoordinateTransport
  FiniteHaarLinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section InnerSpaceCountableBase.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable N : nat.
Variable b : 'I_N -> V.
Hypothesis hb : is_basis b.
Local Notation X := (inner_metric_space hB).

(** Source for [inner_space_countable_open_base]: a finite dimensional
    inner product space has a countable base of open sets, as presupposed
    for Hom(V, V) and its subspaces in Federer 2.7.16, pp. 136–138, by
    2.5.14, p. 107. Supporting lemma: the base consists of the sets
    Psi^{-1}(U_j), where Psi is the inverse of the isometry Phi of R^N
    onto X given by an orthonormal base and U_j is a countable base of
    R^N. *)
Lemma inner_space_countable_open_base : exists U : nat -> set X, is_countable_open_base U.
Proof.
have [e [he hoe]] := orthonormal_basis_exists hB hb.
have ho := orthonormalisation_orthonormal hoe.
have hPhi := orthonormal_synthesis_homeomorphism hB he ho.
have [U hU] := @euclidean_countable_open_base R N.
exists (fun j => (orthonormal_analysis B e : X -> _) @^-1` U j).
apply: (homeomorphic_countable_open_base (homeomorphism_left_inverse hPhi)
  (homeomorphism_right_inverse hPhi) (homeomorphism_continuous hPhi)
  (homeomorphism_inverse_continuous hPhi) hU).
Qed.

End InnerSpaceCountableBase.
