(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg generic_quotient.
From Federer Require Import TensorUP ModuleQuotient Bilinear AlgebraUP
  GradedAlgebra GradedComponents TensorAlgebra TensorGrading TensorPowers
  AlgebraQuotient ExteriorIdeal ExteriorQuotient.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section ExteriorGrading.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation E := (exterior_space V).
Local Notation pi := (quotient_projection (mV V)).

(** Federer 1.3.1, first paragraph: the homogeneous ideal induces the
    direct-sum grading of the exterior algebra. Elements of exterior_power
    are Federer's m-vectors. *)
(** Source for [exterior_grading]: Federer (1969), 1.3.1, p. 13, homogeneous
    ideal and component-quotient displays. In words: The square-generated
    ideal is homogeneous and begins in degree two, so the quotient inherits
    its grading and each component is the corresponding component quotient.
    Definition or construction used to formalise this passage. *)
Definition exterior_grading : grading E :=
  @quotient_grading K (tensor_algebra V) (mV V) (tensor_grading V)
    (@mV_homogeneous K V).
(** Source for [exterior_degree]: Federer (1969), 1.3.1, p. 13, homogeneous
    ideal and component-quotient displays. In words: The square-generated
    ideal is homogeneous and begins in degree two, so the quotient inherits
    its grading and each component is the corresponding component quotient.
    Definition or construction used to formalise this passage. *)
Definition exterior_degree n : {linear E -> E} := grade exterior_grading n.
(** Source for [exterior_power]: Federer (1969), 1.3.1, p. 13, homogeneous
    ideal and component-quotient displays. In words: The square-generated
    ideal is homogeneous and begins in degree two, so the quotient inherits
    its grading and each component is the corresponding component quotient.
    Definition or construction used to formalise this passage. *)
Definition exterior_power n := graded_component exterior_grading n.
HB.instance Definition _ n := GRing.Lmodule.copy (exterior_power n)
  (graded_component exterior_grading n).

(** Source for [exterior_degree_projection]: Federer (1969), 1.3.1, p. 13,
    homogeneous ideal and component-quotient displays. In words: The
    square-generated ideal is homogeneous and begins in degree two, so the
    quotient inherits its grading and each component is the corresponding
    component quotient. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma exterior_degree_projection n x : exterior_degree n (pi x) = pi (tensor_degree n x).
Proof. exact: quotient_gradeE. Qed.

(** Source for [exterior_degree_word]: Federer (1969), 1.3.1, p. 13,
    homogeneous ideal and component-quotient displays. In words: The
    square-generated ideal is homogeneous and begins in degree two, so the
    quotient inherits its grading and each component is the corresponding
    component quotient. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma exterior_degree_word n s :
  exterior_degree n (exterior_word s) = if size s == n then exterior_word s else 0.
Proof.
rewrite /exterior_word exterior_degree_projection tensor_degree_word.
by case: ifP => _; rewrite ?linear0.
Qed.

(** Source for [exterior_degree_orthogonal]: Federer (1969), 1.3.1, p. 13,
    homogeneous ideal and component-quotient displays. In words: The
    square-generated ideal is homogeneous and begins in degree two, so the
    quotient inherits its grading and each component is the corresponding
    component quotient. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma exterior_degree_orthogonal m n x :
  exterior_degree m (exterior_degree n x) = if m == n then exterior_degree n x else 0.
Proof. exact: grade_orthogonal. Qed.
(** Source for [exterior_degree_finite]: Federer (1969), 1.3.1, p. 13,
    homogeneous ideal and component-quotient displays. In words: The
    square-generated ideal is homogeneous and begins in degree two, so the
    quotient inherits its grading and each component is the corresponding
    component quotient. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma exterior_degree_finite x : exists N, x = \sum_(i < N) exterior_degree i x.
Proof. exact: grade_finite. Qed.
(** Source for [exterior_word_homogeneous]: Federer (1969), 1.3.1, p. 13,
    homogeneous ideal and component-quotient displays. In words: The
    square-generated ideal is homogeneous and begins in degree two, so the
    quotient inherits its grading and each component is the corresponding
    component quotient. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma exterior_word_homogeneous s :
  homogeneous exterior_grading (size s) (exterior_word s).
Proof. by rewrite /homogeneous -/(exterior_degree _ _) exterior_degree_word eqxx. Qed.
(** Source for [exterior_unit_homogeneous]: Federer (1969), 1.3.1, p. 13,
    homogeneous ideal and component-quotient displays. In words: The
    square-generated ideal is homogeneous and begins in degree two, so the
    quotient inherits its grading and each component is the corresponding
    component quotient. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma exterior_unit_homogeneous : homogeneous exterior_grading 0 (exterior_unit V).
Proof. exact: (exterior_word_homogeneous [::]). Qed.
(** Source for [exterior_generator_homogeneous]: Federer (1969), 1.3.1, p.
    13, homogeneous ideal and component-quotient displays. In words: The
    square-generated ideal is homogeneous and begins in degree two, so the
    quotient inherits its grading and each component is the corresponding
    component quotient. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma exterior_generator_homogeneous v :
  homogeneous exterior_grading 1 (exterior_generator v).
Proof. exact: (exterior_word_homogeneous [:: v]). Qed.
(** Source for [exterior_projection_graded]: Federer (1969), 1.3.1, p. 13,
    homogeneous ideal and component-quotient displays. In words: The
    square-generated ideal is homogeneous and begins in degree two, so the
    quotient inherits its grading and each component is the corresponding
    component quotient. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma exterior_projection_graded :
  preserves_grading (tensor_grading V) exterior_grading pi.
Proof.
exact: (@quotient_projection_graded K (tensor_algebra V) (mV V)
  (tensor_grading V) (@mV_homogeneous K V)).
Qed.
(** Source for [wedge_graded]: Federer (1969), 1.3.1, p. 13, homogeneous
    ideal and component-quotient displays. In words: The square-generated
    ideal is homogeneous and begins in degree two, so the quotient inherits
    its grading and each component is the corresponding component quotient.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma wedge_graded : graded_product exterior_grading (@wedge K V).
Proof.
exact: (@quotient_mul_graded K (tensor_algebra V) (mV V) (tensor_grading V)
  (@mV_homogeneous K V) (@tensor_product_graded K V)).
Qed.
(** Source for [graded_exterior_algebra]: Federer (1969), 1.3.1, p. 13,
    homogeneous ideal and component-quotient displays. In words: The
    square-generated ideal is homogeneous and begins in degree two, so the
    quotient inherits its grading and each component is the corresponding
    component quotient. Definition or construction used to formalise this
    passage. *)
Definition graded_exterior_algebra : graded_algebra K :=
  @GradedAlgebra K E exterior_grading (@wedge K V) (wedge_bilinear V) wedge_graded.

(** Federer 1.3.1, second paragraph: products of exactly m vectors span
    the space of m-vectors. This induction principle states the full span. *)
(** Source for [exterior_component_induction]: Federer (1969), 1.3.1, p. 13,
    homogeneous ideal and component-quotient displays. In words: The
    square-generated ideal is homogeneous and begins in degree two, so the
    quotient inherits its grading and each component is the corresponding
    component quotient. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma exterior_component_induction n (P : E -> Prop)
    (h0 : P 0) (hD : forall x y, P x -> P y -> P (x + y))
    (hZ : forall a x, P x -> P (a *: x))
    (hw : forall s, size s = n -> P (exterior_word s)) :
    forall x, homogeneous exterior_grading n x -> P x.
Proof.
have hp : forall x, P (exterior_degree n x).
  apply: exterior_word_induction => [|x y hx hy|a x hx|s].
  - by rewrite linear0.
  - rewrite linearD; exact: hD hx hy.
  - rewrite linearZ; exact: hZ hx.
  rewrite exterior_degree_word; case: ifP => [/eqP hs|_]; last exact: h0.
  exact: hw hs.
by move=> x hx; rewrite -hx; exact: hp.
Qed.

End ExteriorGrading.
Arguments exterior_degree {K V} n.
