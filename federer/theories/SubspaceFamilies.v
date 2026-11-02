(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDecomposition.
From Federer Require Import SubspaceCarrier.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1: a prescribed independent family remains independent
    when regarded as a family in any subspace containing it. *)
Section Families.
Variable K : fieldType.
Variable V : lmodType K.
Variable S : subspace V.
Variable I : finType.
Variable e : I -> V.
Hypothesis hS : forall i, S (e i).
(** Source for [subspace_family]: Federer (1969), 1.6.1, p. 23, dimension
    bound, factorisation assertion, and finite-dimensional reduction. In
    words: For a nonzero m-vector the associated space has dimension k<=m;
    the product of any basis of that space factors from the vector, leaving
    degree m-k. Definition or construction used to formalise this passage. *)
Definition subspace_family i := subspace_lift (hS i).
(** Source for [subspace_familyE]: Federer (1969), 1.6.1, p. 23, dimension
    bound, factorisation assertion, and finite-dimensional reduction. In
    words: For a nonzero m-vector the associated space has dimension k<=m;
    the product of any basis of that space factors from the vector, leaving
    degree m-k. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma subspace_familyE i : subspace_val (subspace_family i) = e i.
Proof. by []. Qed.
(** Source for [subspace_family_independent]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Supporting lemma for this passage; not
    separately stated in the book. *)
Theorem subspace_family_independent :
  finite_independent e -> finite_independent subspace_family.
Proof.
move=> he c hc; apply: he.
have h := congr1 (@subspace_val K V S) hc.
rewrite linear_sum linear0 in h.
have hs : (\sum_i subspace_val (c i *: subspace_family i)) = \sum_i c i *: e i.
  apply: eq_bigr => i _; by rewrite linearZ.
by rewrite hs in h.
Qed.
End Families.
