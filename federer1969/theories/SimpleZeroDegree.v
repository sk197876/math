(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDecomposition.
From Federer Require Import AssociatedSubspace SubspaceCarrier.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1, degree-zero boundary of the literal definition. An empty
    exterior product is 1, whereas an arbitrary nonzero zero-vector is a
    scalar. The simplicity/dimension corollary therefore needs m>0. *)
Section ZeroDegree.
Variable K : fieldType.
Variable V : lmodType K.
(** Source for [zeroth_inclusion_val]: Federer (1969), 1.6.1, p. 24, first
    of the four corollaries. In words: The printed corollary identifies
    nonzero simple m-vectors with those whose associated space has dimension
    m, and represents them as products of a suitable basis. Supporting lemma
    for this passage; not separately stated in the book. For the literal
    empty-product definition the reverse implication requires m>0. *)
Lemma zeroth_inclusion_val c :
  component_val (exterior_zeroth_inclusion V c) = exterior_scalar V c.
Proof.
change (exterior_degree 0 ((c : K) *: exterior_unit V) = (c : K) *: exterior_unit V).
by rewrite linearZ (exterior_unit_homogeneous V).
Qed.
(** Source for [empty_e_lambda]: Federer (1969), 1.6.1, p. 24, first of the
    four corollaries. In words: The printed corollary identifies nonzero
    simple m-vectors with those whose associated space has dimension m, and
    represents them as products of a suitable basis. Supporting lemma for
    this passage; not separately stated in the book. For the literal
    empty-product definition the reverse implication requires m>0. *)
Lemma empty_e_lambda : e_lambda (@idfun V) [tuple] = exterior_zeroth_inclusion V 1.
Proof.
apply: val_inj; change (component_val (e_lambda (@idfun V) [tuple]) =
  component_val (exterior_zeroth_inclusion V 1)).
by rewrite e_lambdaE zeroth_inclusion_val /exterior_scalar /= exterior_word_nil scale1r.
Qed.
(** Source for [simple_zero_iff]: Federer (1969), 1.6.1, p. 24, first of the
    four corollaries. In words: The printed corollary identifies nonzero
    simple m-vectors with those whose associated space has dimension m, and
    represents them as products of a suitable basis. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. For the literal empty-product definition the reverse implication
    requires m>0. *)
Theorem simple_zero_iff (xi : exterior_power V 0) :
  simple xi <-> xi = exterior_zeroth_inclusion V 1.
Proof.
split=> [[t ->]|->]; first by rewrite (tuple0 t) empty_e_lambda.
exists [tuple]; exact: esym empty_e_lambda.
Qed.
(** Source for [scalar_associated_zero]: Federer (1969), 1.6.1, p. 24, first
    of the four corollaries. In words: The printed corollary identifies
    nonzero simple m-vectors with those whose associated space has dimension
    m, and represents them as products of a suitable basis. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. For the literal empty-product definition the reverse implication
    requires m>0. *)
Lemma scalar_associated_zero c : c != 0 ->
  forall v, FedererSimple.T (exterior_zeroth_inclusion V c) v <-> v=0.
Proof.
move=> hc v; change (wedge (component_val (exterior_zeroth_inclusion V c))
  (exterior_generator v) = 0 <-> v=0).
rewrite zeroth_inclusion_val /exterior_scalar (bilZl (wedge_bilinear V)) wedge_unitl.
split=> [h|->]; last by rewrite linear0 scaler0.
have hg : exterior_generator v = 0.
  move/eqP: h; rewrite scaler_eq0 (negbTE hc) /=; exact: eqP.
apply: exterior_generator_injective; by rewrite linear0.
Qed.
(** Source for [scalar_not_simple]: Federer (1969), 1.6.1, p. 24, first of
    the four corollaries. In words: The printed corollary identifies nonzero
    simple m-vectors with those whose associated space has dimension m, and
    represents them as products of a suitable basis. Local counterexample or
    necessary correction to the printed assertion, not a claim of the book.
    For the literal empty-product definition the reverse implication
    requires m>0. *)
Theorem scalar_not_simple c : c != 1 -> ~ simple (exterior_zeroth_inclusion V c).
Proof.
move=> hc /simple_zero_iff h.
have he : c = 1 := can_inj (exterior_zeroth_inclusionK V) h.
by move: hc; rewrite he eqxx.
Qed.
(** Source for [scalar_mvector_nonzero]: Federer (1969), 1.6.1, p. 24, first
    of the four corollaries. In words: The printed corollary identifies
    nonzero simple m-vectors with those whose associated space has dimension
    m, and represents them as products of a suitable basis. Supporting lemma
    for this passage; not separately stated in the book. For the literal
    empty-product definition the reverse implication requires m>0. *)
Lemma scalar_mvector_nonzero c : c != 0 -> exterior_zeroth_inclusion V c != 0.
Proof.
move=> hc; apply/eqP=> h.
have he : c = 0.
  apply: (can_inj (exterior_zeroth_inclusionK V)).
  by rewrite linear0 h.
by move: hc; rewrite he eqxx.
Qed.
Variable c : K.
Hypothesis hc : c != 0.
Local Notation T := (FedererSimple.T (exterior_zeroth_inclusion V c)).
Local Notation U := (subspace_space T).
(** Source for [scalar_associated_space_zero]: Federer (1969), 1.6.1, p. 24,
    first of the four corollaries. In words: The printed corollary
    identifies nonzero simple m-vectors with those whose associated space
    has dimension m, and represents them as products of a suitable basis.
    Supporting lemma for this passage; not separately stated in the book.
    For the literal empty-product definition the reverse implication
    requires m>0. *)
Lemma scalar_associated_space_zero (u : U) : u = 0.
Proof.
apply: val_inj; change (subspace_val u = subspace_val (0 : U)).
rewrite linear0; exact: (proj1 (scalar_associated_zero hc (subspace_val u)) (subspace_valP u)).
Qed.
(** Source for [scalar_associated_basis]: Federer (1969), 1.6.1, p. 24,
    first of the four corollaries. In words: The printed corollary
    identifies nonzero simple m-vectors with those whose associated space
    has dimension m, and represents them as products of a suitable basis.
    Definition or construction used to formalise this passage. For the
    literal empty-product definition the reverse implication requires m>0. *)
Definition scalar_associated_basis (_ : 'I_0) : U := 0.
(** Source for [scalar_associated_basisP]: Federer (1969), 1.6.1, p. 24,
    first of the four corollaries. In words: The printed corollary
    identifies nonzero simple m-vectors with those whose associated space
    has dimension m, and represents them as products of a suitable basis.
    Supporting lemma for this passage; not separately stated in the book.
    For the literal empty-product definition the reverse implication
    requires m>0. *)
Lemma scalar_associated_basisP : is_basis scalar_associated_basis.
Proof.
apply: finite_basis_criterion.
- move=> d hd i; by have := ltn_ord i; rewrite ltn0.
- move=> u; exists (fun _ => 0); rewrite big_ord0; exact: scalar_associated_space_zero.
Qed.
(** Source for [scalar_associated_dimension]: Federer (1969), 1.6.1, p. 24,
    first of the four corollaries. In words: The printed corollary
    identifies nonzero simple m-vectors with those whose associated space
    has dimension m, and represents them as products of a suitable basis.
    Supporting lemma for this passage; not separately stated in the book.
    For the literal empty-product definition the reverse implication
    requires m>0. *)
Lemma scalar_associated_dimension : dim (finite_basis_vect scalar_associated_basisP) = 0%N.
Proof. by rewrite finite_basis_dimension card_ord. Qed.
(** Federer 1.6.1: a checked counterexample to including degree zero in
    the first corollary, while keeping the printed definition literally. *)
(** Source for [zero_degree_simplicity_exception]: Federer (1969), 1.6.1, p.
    24, first of the four corollaries. In words: The printed corollary
    identifies nonzero simple m-vectors with those whose associated space
    has dimension m, and represents them as products of a suitable basis.
    Local counterexample or necessary correction to the printed assertion,
    not a claim of the book. For the literal empty-product definition the
    reverse implication requires m>0. *)
Theorem zero_degree_simplicity_exception : c != 1 ->
  exterior_zeroth_inclusion V c != 0 /\
  dim (finite_basis_vect scalar_associated_basisP) = 0%N /\
  ~ simple (exterior_zeroth_inclusion V c).
Proof.
move=> hc1; split; first exact: scalar_mvector_nonzero.
split; [exact: scalar_associated_dimension | exact: scalar_not_simple].
Qed.
End ZeroDegree.
