(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp functions.
From Federer Require Import SimpleVectors.
From Federer Require Import NonzeroSimple SubspaceEquality GrassmannSubspaces SubspaceBasisProduct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.2, first sentence: the association of 1.6.1 maps the
    set of all nonzero simple m-vectors onto G(V,m). *)
(** Source for [associated_G_surjective]: Federer (1969), 1.6.2, p. 24,
    first sentence, surjectivity of the association. In words: Every
    m-dimensional subspace is the associated subspace of a nonzero simple
    m-vector, obtained by taking the exterior product of a basis. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem associated_G_surjective (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) m : forall S : G V m, exists xi, associated_G h2 xi = S.
Proof.
move=> S; have [e he] := grassmann_proof S.
pose xi := subspace_basis_product e.
have hx : xi != 0 := subspace_basis_product_nonzero h2 he.
have hs : simple xi := subspace_basis_product_simple e.
exists (@nonzero_simple_lift K V m xi hx hs).
apply: grassmann_ext => v.
change (FedererSimple.T xi v <-> grassmann_val S v).
exact (@subspace_basis_product_associated K h2 V (grassmann_val S) m e he v).
Qed.
