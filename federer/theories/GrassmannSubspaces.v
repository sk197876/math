(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import SimpleVectors.
From Federer Require Import NonzeroSimple SubspaceEquality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.2: G(V,m) is the set of all m-dimensional vector
    subspaces of V. Finite dimension is expressed by an actual basis
    of the carrier, without an ambient finite-dimensionality assumption. *)
Section Grassmann.
Variable K : fieldType.
Variable V : lmodType K.
Variable m : nat.
(** Source for [grassmann_pred]: Federer (1969), 1.6.2, p. 24, opening
    paragraph defining G(V,m). In words: The association from nonzero simple
    m-vectors is onto the set of m-dimensional subspaces; its fibres are
    nonzero scalar proportionality classes. Definition or construction used
    to formalise this passage. *)
Definition grassmann_pred (S : subspace V) :=
  exists e : 'I_m -> subspace_space S, is_basis e.
(** Source for [G]: Federer (1969), 1.6.2, p. 24, opening paragraph defining
    G(V,m). In words: The association from nonzero simple m-vectors is onto
    the set of m-dimensional subspaces; its fibres are nonzero scalar
    proportionality classes. Definition or construction used to formalise
    this passage. *)
Record G := GrassmannSubspace {
  grassmann_val : subspace V;
  grassmann_proof : grassmann_pred grassmann_val
}.
(** Source for [grassmann_ext]: Federer (1969), 1.6.2, p. 24, opening
    paragraph defining G(V,m). In words: The association from nonzero simple
    m-vectors is onto the set of m-dimensional subspaces; its fibres are
    nonzero scalar proportionality classes. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Lemma grassmann_ext (S T : G) :
  (forall v, grassmann_val S v <-> grassmann_val T v) -> S=T.
Proof.
case: S => S hS; case: T => T hT /= h.
have he : S=T := subspace_ext h; subst S.
congr (@GrassmannSubspace T _); exact: Prop_irrelevance.
Qed.
Hypothesis h2 : (1+1 : K) != 0.
(** Source for [associated_G]: Federer (1969), 1.6.2, p. 24, opening
    paragraph defining G(V,m). In words: The association from nonzero simple
    m-vectors is onto the set of m-dimensional subspaces; its fibres are
    nonzero scalar proportionality classes. Definition or construction used
    to formalise this passage. *)
Definition associated_G (xi : nonzero_simple V m) : G.
Proof.
apply: (@GrassmannSubspace (FedererSimple.T (simple_val xi))).
have [e [he _]] := @simple_is_basis_product K h2 V m (simple_val xi)
  (simple_val_nonzero xi) (simple_val_simple xi).
by exists e.
Defined.
(** Source for [associated_GE]: Federer (1969), 1.6.2, p. 24, opening
    paragraph defining G(V,m). In words: The association from nonzero simple
    m-vectors is onto the set of m-dimensional subspaces; its fibres are
    nonzero scalar proportionality classes. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Lemma associated_GE xi v :
  grassmann_val (associated_G xi) v <-> FedererSimple.T (simple_val xi) v.
Proof. by []. Qed.
End Grassmann.
Arguments G {K} V m.
Arguments grassmann_val {K V m} _.
