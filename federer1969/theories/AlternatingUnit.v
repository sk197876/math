(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Alternating.
From Federer Require Import Convolution ExteriorCounit AlternatingProduct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.2, unit assertion: W embeds as constant degree-zero forms.
    A unit of W is a unit of the alternating algebra. *)
Section Coefficients.
Variable K : fieldType.
Variables V W : lmodType K.
(** Source for [coefficient_form]: Federer (1969), 1.4.2, p. 18, third
    consequence of the diagonal properties. In words: A multiplicative unit
    in the coefficient algebra is a degree-zero unit for the alternating
    product. Definition or construction used to formalise this passage. *)
Definition coefficient_form (w : W) : A_star V W := form_include (zero_form V w).
(** Source for [coefficient_formE]: Federer (1969), 1.4.2, p. 18, third
    consequence of the diagonal properties. In words: A multiplicative unit
    in the coefficient algebra is a degree-zero unit for the alternating
    product. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Lemma coefficient_formE w x : coefficient_form w x = (exterior_augmentation V x : K) *: w.
Proof.
elim/exterior_word_induction: x => [|x y hx hy|c x hx|s].
- by rewrite !linear0 scale0r.
- rewrite !linearD; change (coefficient_form w x + coefficient_form w y =
    ((exterior_augmentation V x : K) + exterior_augmentation V y) *: w).
  by rewrite hx hy scalerDl.
- rewrite !linearZ; change (c *: coefficient_form w x =
    (c * (exterior_augmentation V x : K)) *: w).
  by rewrite hx scalerA.
- rewrite /coefficient_form form_includeE form_extensionE exterior_augmentation_word.
  case: s => [|v s].
  + change (form_words (zero_form V w) [tuple] = (1 : K) *: w).
    by rewrite form_wordsE zero_formE scale1r.
  + rewrite form_words_wrong //; by rewrite /word_degree_zero scale0r.
Qed.
(** Source for [coefficient_form_linear]: Federer (1969), 1.4.2, p. 18,
    third consequence of the diagonal properties. In words: A multiplicative
    unit in the coefficient algebra is a degree-zero unit for the
    alternating product. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma coefficient_form_linear : linear coefficient_form.
Proof. move=> c v w; by rewrite /coefficient_form !linearP. Qed.
HB.instance Definition _ := GRing.isLinear.Build K W (A_star V W)
  *:%R coefficient_form coefficient_form_linear.
(** Source for [coefficient_form_homogeneous]: Federer (1969), 1.4.2, p. 18,
    third consequence of the diagonal properties. In words: A multiplicative
    unit in the coefficient algebra is a degree-zero unit for the
    alternating product. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma coefficient_form_homogeneous w : homogeneous (A_star_grading V W) 0 (coefficient_form w).
Proof. exact: form_include_homogeneous. Qed.
End Coefficients.

Section Unit.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variables V W : lmodType K.
Variable mu : W -> W -> W.
Hypothesis hmu : bilinear mu.
Variable u : W.
Local Notation E := (exterior_space V).
Local Notation U := (coefficient_form V u).
(** Source for [coefficient_left_unit_tensor]: Federer (1969), 1.4.2, p. 18,
    third consequence of the diagonal properties. In words: A multiplicative
    unit in the coefficient algebra is a degree-zero unit for the
    alternating product. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma coefficient_left_unit_tensor : left_id u mu -> forall (a : Hom E W) x,
  paired_tensor hmu U a x = a (counit_left V x).
Proof.
move=> hu a x; apply: (tensor_ext (tensor_exists E E) (paired_tensor hmu U a)
  (linear_comp (hom_as_linear a) (counit_left V))) x => v w.
change (paired_tensor hmu U a (tensor_inj v w) = a (counit_left V (tensor_inj v w))).
rewrite paired_tensorE coefficient_formE counit_leftE (bilZl hmu) hu.
exact (esym (linZ (hom_linear a) (exterior_augmentation V v : K) w)).
Qed.
(** Source for [coefficient_right_unit_tensor]: Federer (1969), 1.4.2, p.
    18, third consequence of the diagonal properties. In words: A
    multiplicative unit in the coefficient algebra is a degree-zero unit for
    the alternating product. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma coefficient_right_unit_tensor : right_id u mu -> forall (a : Hom E W) x,
  paired_tensor hmu a U x = a (counit_right V x).
Proof.
move=> hu a x; apply: (tensor_ext (tensor_exists E E) (paired_tensor hmu a U)
  (linear_comp (hom_as_linear a) (counit_right V))) x => v w.
change (paired_tensor hmu a U (tensor_inj v w) = a (counit_right V (tensor_inj v w))).
rewrite paired_tensorE coefficient_formE counit_rightE (bilZr hmu) hu.
exact (esym (linZ (hom_linear a) (exterior_augmentation V w : K) v)).
Qed.
(** Source for [alternating_unit_left]: Federer (1969), 1.4.2, p. 18, third
    consequence of the diagonal properties. In words: A multiplicative unit
    in the coefficient algebra is a degree-zero unit for the alternating
    product. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Theorem alternating_unit_left : left_id u mu -> left_id U (alternating_wedge h2 hmu).
Proof.
move=> hu a; apply: hom_finite_ext => x.
by rewrite alternating_wedgeE (coefficient_left_unit_tensor hu) counit_left_Psi.
Qed.
(** Source for [alternating_unit_right]: Federer (1969), 1.4.2, p. 18, third
    consequence of the diagonal properties. In words: A multiplicative unit
    in the coefficient algebra is a degree-zero unit for the alternating
    product. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Theorem alternating_unit_right : right_id u mu -> right_id U (alternating_wedge h2 hmu).
Proof.
move=> hu a; apply: hom_finite_ext => x.
by rewrite alternating_wedgeE (coefficient_right_unit_tensor hu) counit_right_Psi.
Qed.
End Unit.

Section UnitalAlgebra.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable W : algebra K.
(** Source for [alternating_unital_algebra]: Federer (1969), 1.4.2, p. 18,
    third consequence of the diagonal properties. In words: A multiplicative
    unit in the coefficient algebra is a degree-zero unit for the
    alternating product. Definition or construction used to formalise this
    passage. *)
Definition alternating_unital_algebra : algebra K :=
  @Algebra K (A_star V W) (alternating_wedge h2 (alg_bilinear W))
    (coefficient_form V (alg_one W))
    (@alternating_wedge_bilinear K h2 V W (alg_mul W) (alg_bilinear W))
    (@alternating_wedge_associative K h2 V W (alg_mul W) (alg_bilinear W) (@alg_assoc K W))
    (@alternating_unit_left K h2 V W (alg_mul W) (alg_bilinear W) (alg_one W) (@alg_unitl K W))
    (@alternating_unit_right K h2 V W (alg_mul W) (alg_bilinear W) (alg_one W) (@alg_unitr K W)).
(** Source for [alternating_unital]: Federer (1969), 1.4.2, p. 18, third
    consequence of the diagonal properties. In words: A multiplicative unit
    in the coefficient algebra is a degree-zero unit for the alternating
    product. Definition or construction used to formalise this passage. *)
Definition alternating_unital : unital_graded_algebra K :=
  @UnitalGradedAlgebra K alternating_unital_algebra (A_star_grading V W)
    (@alternating_wedge_graded K h2 V W (alg_mul W) (alg_bilinear W)).
End UnitalAlgebra.
