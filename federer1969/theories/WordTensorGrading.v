(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg finmap generic_quotient.
From Federer Require Import TensorUP FreeVector ModuleQuotient Bilinear
  AlgebraUP WordEvaluation WordAlgebra WordTensorAlgebra GradedAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section WordGrading.
Variable K : fieldType.
Variable X : choiceType.
Local Notation F := (word_space K X).
Local Notation d := (word_delta K (X := X)).

(** Source for [word_grade]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition word_grade n : {linear F -> F} := GRing.Linear.clone _ _ _ _
  (free_extend (fun s : seq X => if size s == n then d s else 0)) _.

(** Source for [word_gradeE]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_gradeE n s : word_grade n (d s) = if size s == n then d s else 0.
Proof. exact: free_extend_delta. Qed.

(** Source for [word_grade_orthogonal]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_grade_orthogonal m n x :
  word_grade m (word_grade n x) = if m == n then word_grade n x else 0.
Proof.
elim/free_induction: x => [|x y hx hy|a x hx|s].
- by rewrite !linear0; case: ifP.
- rewrite !linearD /= hx hy; by case: ifP; rewrite ?add0r.
- rewrite !linearZ /= hx; by case: ifP; rewrite ?scaler0.
rewrite word_gradeE; case hs: (size s == n).
  move/eqP: hs => <-; by rewrite word_gradeE eq_sym.
by rewrite linear0; case: ifP.
Qed.

(** Source for [word_bound]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition word_bound (x : F) := (\max_(s <- finsupp x) size s).+1.

(** Source for [word_grade_finite]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_grade_finite x : x = \sum_(i < word_bound x) word_grade i x.
Proof.
rewrite {1}(free_expansion x).
under [RHS]eq_bigr do rewrite /word_grade /= /free_extend.
rewrite exchange_big; apply: eq_big_seq => s hs.
rewrite -scaler_sumr.
have hbound : (size s < word_bound x)%N.
  apply: leq_bigmax_seq; first exact: hs.
  by [].
under eq_bigr do rewrite eq_sym.
rewrite -big_mkcond.
by rewrite (big_pred1 (Ordinal hbound)).
Qed.
End WordGrading.
Arguments word_grade {K X} n.

Section TensorGrading.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation X := (Choice.clone V _).
Local Notation F := (word_space K X).
Local Notation T := (tensor_algebra_space V).
Local Notation S := (word_subspace V).
Local Notation pi := (quotient_projection S).

(** Source for [word_relation_grade]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_relation_grade n (x : F) : word_relation x -> word_relation (word_grade n x).
Proof.
elim=> [|x' y hx ihx hy ihy|a x' hx ihx|s t v w|s t a v].
- by rewrite linear0; exact: wr_zero.
- rewrite linearD; exact: wr_add ihx ihy.
- rewrite linearZ; exact: wr_scale ihx.
- rewrite linearB linearD /= !word_gradeE !size_cat /=.
  case: ifP => _; first exact: wr_linear_add.
  by rewrite addr0 subrr; exact: wr_zero.
- rewrite linearB linearZ /= !word_gradeE !size_cat /=.
  case: ifP => _; first exact: wr_linear_scale.
  by rewrite scaler0 subrr; exact: wr_zero.
Qed.

(** Source for [word_grade_projection]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition word_grade_projection n : {linear F -> T} :=
  linear_comp (GRing.Linear.clone _ _ _ _ pi _) (word_grade n).

(** Source for [word_grade_killed]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma word_grade_killed n x : S x -> word_grade_projection n x = 0.
Proof.
move=> hx; change (pi (word_grade n x) = 0).
rewrite -(linear0 pi); apply/quotient_projection_eq; rewrite subr0.
exact: word_relation_grade hx.
Qed.

(** Source for [tensor_degree]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_degree n : {linear T -> T} := GRing.Linear.clone _ _ _ _
  (quotient_lift (S := S) (f := word_grade_projection n) (word_grade_killed n)) _.

(** Source for [tensor_degreeE]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_degreeE n x : tensor_degree n (pi x) = pi (word_grade n x).
Proof. exact: quotient_liftE. Qed.

(** Source for [tensor_degree_word]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_degree_word n s :
  tensor_degree n (tensor_word s) = if size s == n then tensor_word s else 0.
Proof.
rewrite /tensor_word tensor_degreeE word_gradeE.
by case: ifP => _; rewrite ?linear0.
Qed.

(** Source for [tensor_degree_orthogonal]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_degree_orthogonal m n x :
  tensor_degree m (tensor_degree n x) = if m == n then tensor_degree n x else 0.
Proof.
rewrite -[x]quotient_projection_surjective !tensor_degreeE word_grade_orthogonal.
by case: ifP => _; rewrite ?linear0.
Qed.

(** Source for [tensor_degree_finite]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma tensor_degree_finite x : exists N, x = \sum_(i < N) tensor_degree i x.
Proof.
exists (word_bound (repr x)).
rewrite -{1}[x]quotient_projection_surjective {1}(word_grade_finite (repr x)) linear_sum /=.
apply: eq_bigr => i _.
by rewrite -tensor_degreeE quotient_projection_surjective.
Qed.

(** Source for [tensor_grading]: Federer (1969), 1.2.3, p. 12, opening
    construction and multiplication paragraphs. In words: The tensor algebra
    is the direct sum of tensor powers, with degree zero equal to R and
    degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition tensor_grading : grading T :=
  @Grading K T tensor_degree tensor_degree_orthogonal tensor_degree_finite.

(** Source for [tensor_word_homogeneous]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_word_homogeneous s : homogeneous tensor_grading (size s) (tensor_word s).
Proof.
change (tensor_degree (size s) (tensor_word s) = tensor_word s).
by rewrite tensor_degree_word eqxx.
Qed.

(** Source for [tensor_unit_homogeneous]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_unit_homogeneous : homogeneous tensor_grading 0 (tensor_unit V).
Proof. exact: (tensor_word_homogeneous [::]). Qed.

(** Source for [tensor_generator_homogeneous]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_generator_homogeneous v : homogeneous tensor_grading 1 (tensor_generator v).
Proof. exact: (tensor_word_homogeneous [:: v]). Qed.

(** Source for [tensor_product_components]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_product_components m n x y :
  homogeneous tensor_grading (m + n)%N (tensor_product (tensor_degree m x) (tensor_degree n y)).
Proof.
move: x y; apply: tensor_word_induction => [y|x x' hx hx' y|a x hx y|s].
- rewrite linear0 (bil0l (tensor_product_bilinear V)); exact: homogeneous0.
- rewrite linearD (bilDl (tensor_product_bilinear V)); exact: homogeneousD (hx y) (hx' y).
- rewrite linearZ (bilZl (tensor_product_bilinear V)); exact: homogeneousZ (hx y).
apply: tensor_word_induction => [|y y' hy hy'|a y hy|t].
- rewrite linear0 (bil0r (tensor_product_bilinear V)); exact: homogeneous0.
- rewrite linearD (bilDr (tensor_product_bilinear V)); exact: homogeneousD hy hy'.
- rewrite linearZ (bilZr (tensor_product_bilinear V)); exact: homogeneousZ hy.
rewrite !tensor_degree_word.
case hs: (size s == m); last first.
  rewrite (bil0l (tensor_product_bilinear V)); exact: homogeneous0.
case ht: (size t == n); last first.
  rewrite (bil0r (tensor_product_bilinear V)); exact: homogeneous0.
rewrite tensor_product_words; move/eqP: hs => <-; move/eqP: ht => <-.
rewrite -size_cat; exact: tensor_word_homogeneous.
Qed.

(** Source for [tensor_product_graded]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma tensor_product_graded : graded_product tensor_grading (@tensor_product K V).
Proof.
move=> m n x y hx hy.
rewrite -hx -hy; exact: tensor_product_components.
Qed.

(** Source for [graded_tensor_algebra]: Federer (1969), 1.2.3, p. 12,
    opening construction and multiplication paragraphs. In words: The tensor
    algebra is the direct sum of tensor powers, with degree zero equal to R
    and degree one equal to V; multiplication groups tensor factors, is
    associative, and has unit one. Definition or construction used to
    formalise this passage. *)
Definition graded_tensor_algebra : graded_algebra K :=
  @GradedAlgebra K T tensor_grading (@tensor_product K V) (tensor_product_bilinear V)
    tensor_product_graded.
End TensorGrading.
Arguments tensor_degree {K V} n.
