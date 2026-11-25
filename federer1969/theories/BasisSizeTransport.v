(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDecomposition.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Federer 1.6.1: express a basis of known dimension using precisely
    that many ordinal indices; no basis vectors are changed. *)
(** Source for [basis_cast_size]: Federer (1969), 1.6.1, p. 23, dimension
    bound, factorisation assertion, and finite-dimensional reduction. In
    words: For a nonzero m-vector the associated space has dimension k<=m;
    the product of any basis of that space factors from the vector, leaving
    degree m-k. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma basis_cast_size (K : fieldType) (V : lmodType K) k m
  (h : k=m) (e : 'I_k -> V) :
  is_basis e -> is_basis (fun i : 'I_m => e (cast_ord (esym h) i)).
Proof.
move=> he.
apply: (@basis_reindex K (Choice.clone 'I_k _) (Choice.clone 'I_m _) V
  e he (cast_ord h) (cast_ord (esym h))) => i; exact: val_inj.
Qed.
