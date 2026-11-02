(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import InteriorDecomposition.
From Federer Require Import SubspaceCarrier FiniteSpans.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1, finite-dimensional reduction: the span of a finite
    independent family carries that family as an actual finite basis. *)
Section Span.
Variable K : fieldType.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
(** Source for [finite_span_subspace]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Definition or construction used to formalise
    this passage. *)
Definition finite_span_subspace : subspace V :=
  @Subspace K V (in_finite_span e) (in_finite_span_zero e)
    (@in_finite_span_add K V n e) (@in_finite_span_scale K V n e).
(** Source for [finite_span_generator]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma finite_span_generator i : finite_span_subspace (e i).
Proof.
exists (fun j => delta K i j).
have h := @basis_synthesisE K (Choice.clone 'I_n _) V e i.
by rewrite basis_synthesis_finiteE in h; symmetry.
Qed.
(** Source for [finite_span_basis]: Federer (1969), 1.6.1, p. 23, dimension
    bound, factorisation assertion, and finite-dimensional reduction. In
    words: For a nonzero m-vector the associated space has dimension k<=m;
    the product of any basis of that space factors from the vector, leaving
    degree m-k. Definition or construction used to formalise this passage. *)
Definition finite_span_basis i : subspace_space finite_span_subspace :=
  subspace_lift (finite_span_generator i).
(** Source for [finite_span_basisE]: Federer (1969), 1.6.1, p. 23, dimension
    bound, factorisation assertion, and finite-dimensional reduction. In
    words: For a nonzero m-vector the associated space has dimension k<=m;
    the product of any basis of that space factors from the vector, leaving
    degree m-k. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma finite_span_basisE i : subspace_val (finite_span_basis i) = e i.
Proof. by []. Qed.
Hypothesis he : finite_independent e.
(** Source for [finite_span_independent]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma finite_span_independent : finite_independent finite_span_basis.
Proof.
move=> c hc; apply: he.
have h := congr1 (@subspace_val K V finite_span_subspace) hc.
rewrite linear_sum linear0 in h.
have hs : (\sum_i subspace_val (c i *: finite_span_basis i)) = \sum_i c i *: e i.
  apply: eq_bigr => i _; by rewrite linearZ.
by rewrite hs in h.
Qed.
(** Source for [finite_span_basisP]: Federer (1969), 1.6.1, p. 23, dimension
    bound, factorisation assertion, and finite-dimensional reduction. In
    words: For a nonzero m-vector the associated space has dimension k<=m;
    the product of any basis of that space factors from the vector, leaving
    degree m-k. Supporting lemma for this passage; not separately stated in
    the book. *)
Theorem finite_span_basisP : is_basis finite_span_basis.
Proof.
apply: finite_basis_criterion finite_span_independent _ => v.
have [c hc] := subspace_valP v.
exists c; apply: val_inj; change
  (subspace_val v = subspace_val (\sum_i c i *: finite_span_basis i)).
rewrite linear_sum hc; apply: eq_bigr => i _.
by rewrite linearZ.
Qed.
(** Source for [finite_span_vect]: Federer (1969), 1.6.1, p. 23, dimension
    bound, factorisation assertion, and finite-dimensional reduction. In
    words: For a nonzero m-vector the associated space has dimension k<=m;
    the product of any basis of that space factors from the vector, leaving
    degree m-k. Definition or construction used to formalise this passage. *)
Definition finite_span_vect : vectType K := finite_basis_vect finite_span_basisP.
(** Source for [finite_span_dimension]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma finite_span_dimension : dim finite_span_vect = n.
Proof. by rewrite /finite_span_vect finite_basis_dimension card_ord. Qed.
End Span.
