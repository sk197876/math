(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP Bilinear AlgebraUP GradedAlgebra WordEvaluation
  TensorAlgebraUP TensorAlgebraSealed TensorAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.2.3: the grading of the tensor algebra by word length, from
    [is_graded_tensor_algebra]. *)
Section TensorGrading.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation T := (tensor_algebra_space V).

(** Source for [tensor_degree]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_degree n : {linear T -> T} := grade (tensor_grading V) n.

(** Source for [tensor_word_homogeneous]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_word_homogeneous s : homogeneous (tensor_grading V) (size s) (tensor_word s).
Proof. exact: word_homogeneous (tensor_algebraP V) s. Qed.

(** Source for [tensor_degree_word]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_degree_word n s :
  tensor_degree n (tensor_word s) = if size s == n then tensor_word s else 0.
Proof.
rewrite /tensor_degree (grade_homogeneous _ (tensor_word_homogeneous s)).
by rewrite eq_sym.
Qed.

(** Source for [tensor_degree_orthogonal]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_degree_orthogonal m n x :
  tensor_degree m (tensor_degree n x) = if m == n then tensor_degree n x else 0.
Proof. exact: grade_orthogonal. Qed.

(** Source for [tensor_degree_finite]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma tensor_degree_finite x : exists N, x = \sum_(i < N) tensor_degree i x.
Proof. exact: grade_finite. Qed.

(** Source for [tensor_unit_homogeneous]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_unit_homogeneous : homogeneous (tensor_grading V) 0 (tensor_unit V).
Proof. exact: (tensor_word_homogeneous [::]). Qed.

(** Source for [tensor_generator_homogeneous]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_generator_homogeneous v :
  homogeneous (tensor_grading V) 1 (tensor_generator v).
Proof. exact: (tensor_word_homogeneous [:: v]). Qed.

(** Source for [tensor_product_components]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_product_components m n x y :
  homogeneous (tensor_grading V) (m + n)%N
    (tensor_product (tensor_degree m x) (tensor_degree n y)).
Proof.
have b := tensor_product_bilinear V.
elim/tensor_word_induction: x => [|x x' hx hx'|a x hx|s].
- by rewrite linear0 (bil0l b); exact: homogeneous0.
- by rewrite linearD (bilDl b); exact: homogeneousD.
- by rewrite linearZ (bilZl b); exact: homogeneousZ.
elim/tensor_word_induction: y => [|y y' hy hy'|a y hy|t].
- by rewrite linear0 (bil0r b); exact: homogeneous0.
- by rewrite linearD (bilDr b); exact: homogeneousD.
- by rewrite linearZ (bilZr b); exact: homogeneousZ.
rewrite !tensor_degree_word.
case: (eqVneq (size s) m) => [<-|_]; last first.
  by rewrite (bil0l b); exact: homogeneous0.
case: (eqVneq (size t) n) => [<-|_]; last first.
  by rewrite (bil0r b); exact: homogeneous0.
by rewrite tensor_product_words -size_cat; exact: tensor_word_homogeneous.
Qed.

(** Source for [tensor_product_graded]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma tensor_product_graded : graded_product (tensor_grading V) (@tensor_product K V).
Proof.
move=> m n x y hx hy.
by rewrite -hx -hy; exact: tensor_product_components.
Qed.

(** Source for [graded_tensor_algebra]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition graded_tensor_algebra : graded_algebra K :=
  @GradedAlgebra K T (tensor_grading V) (@tensor_product K V)
    (tensor_product_bilinear V) tensor_product_graded.

End TensorGrading.
Arguments tensor_degree {K V} n.
