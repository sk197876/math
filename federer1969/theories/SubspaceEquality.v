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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Federer 1.6.2: equality in the set of subspaces is precisely
    extensional equality of their membership predicates. *)
(** Source for [subspace_ext]: Federer (1969), 1.6.2, p. 24, opening
    paragraph defining G(V,m). In words: The association from nonzero simple
    m-vectors is onto the set of m-dimensional subspaces; its fibres are
    nonzero scalar proportionality classes. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Lemma subspace_ext (K : fieldType) (V : lmodType K) (S T : subspace V) :
  (forall v, S v <-> T v) -> S=T.
Proof.
case: S => s s0 sD sZ; case: T => t t0 tD tZ /= h.
have he : s=t by apply: funext => v; exact: propext (h v).
subst t; congr (@Subspace K V s _ _ _); exact: Prop_irrelevance.
Qed.
