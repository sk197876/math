(** Federer (1969), 1.10.2, p. 45: units in symmetric-form algebras. Left
    and right unit assertions do not assume associativity. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Graded UnitalGradedTensor Hom HomogeneousHom
  BoundedHom Convolution TensorPowers SymmetricAlgebra SymmetricGrading
  SymmetricDirectSum SymmetricDiagonal SymmetricCounit SymmetricForms
  SymmetricFormWords SymmetricFormExtension SymmetricFormIsomorphism
  SymmetricFormZero SymmetricFormSum SymmetricFormDual SymmetricFormProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Coefficients.
Variable K : fieldType.
Variables V W : lmodType K.
(** Source for [symmetric_coefficient_form]: Federer 1.10.2, p. 45,
    sentence asserting inheritance of a unit. In words: Regard a coefficient as a homogeneous symmetric form of degree zero. *)
Definition symmetric_coefficient_form (w : W) : S_star V W := sform_include (zero_sform V w).
(** Source for [symmetric_coefficient_formE]: Federer 1.10.2, p. 45,
    sentence asserting inheritance of a unit. In words: Evaluation of a constant form is its coefficient multiplied by augmentation. *)
Lemma symmetric_coefficient_formE w x : symmetric_coefficient_form w x = (symmetric_augmentation V x : K) *: w.
Proof.
elim/symmetric_word_induction: x => [|x y hx hy|c x hx|s].
- by rewrite !linear0 scale0r.
- rewrite !linearD; change (symmetric_coefficient_form w x + symmetric_coefficient_form w y =
    ((symmetric_augmentation V x : K) + symmetric_augmentation V y) *: w).
  by rewrite hx hy scalerDl.
- rewrite !linearZ; change (c *: symmetric_coefficient_form w x =
    (c * (symmetric_augmentation V x : K)) *: w).
  by rewrite hx scalerA.
- rewrite /symmetric_coefficient_form sform_includeE sform_extensionE symmetric_augmentation_word.
  case: s => [|v s].
  + change (sform_words (zero_sform V w) [tuple] = (1 : K) *: w).
    by rewrite sform_wordsE zero_sformE scale1r.
  + rewrite sform_words_wrong //; by rewrite /word_degree_zero scale0r.
Qed.
(** Source for [symmetric_coefficient_form_linear]: Federer 1.10.2, p. 45,
    sentence asserting inheritance of a unit. In words: The coefficient inclusion is linear. *)
Lemma symmetric_coefficient_form_linear : linear symmetric_coefficient_form.
Proof. move=> c v w; by rewrite /symmetric_coefficient_form !linearP. Qed.
HB.instance Definition _ := GRing.isLinear.Build K W (S_star V W)
  *:%R symmetric_coefficient_form symmetric_coefficient_form_linear.
(** Source for [symmetric_coefficient_form_homogeneous]: Federer 1.10.2, p. 45,
    sentence asserting inheritance of a unit. In words: A coefficient form is homogeneous of degree zero. *)
Lemma symmetric_coefficient_form_homogeneous w : homogeneous (S_star_grading V W) 0 (symmetric_coefficient_form w).
Proof. exact: sform_include_homogeneous. Qed.
End Coefficients.

Section Unit.
Variable K : fieldType.
Variables V W : lmodType K.
Variable mu : W -> W -> W.
Hypothesis hmu : bilinear mu.
Variable u : W.
Local Notation E := (symmetric_space V).
Local Notation U := (symmetric_coefficient_form V u).
(** Source for [symmetric_coefficient_left_unit_tensor]: Federer 1.10.2, p. 45,
    sentence asserting inheritance of a unit. In words: Supporting counit calculation when the coefficient is a left unit. *)
Lemma symmetric_coefficient_left_unit_tensor : left_id u mu -> forall (a : Hom E W) x,
  paired_tensor hmu U a x = a (symmetric_counit_left V x).
Proof.
move=> hu a x; apply: (tensor_ext (tensor_exists E E) (paired_tensor hmu U a)
  (linear_comp (hom_as_linear a) (symmetric_counit_left V))) x => v w.
change (paired_tensor hmu U a (tensor_inj v w) = a (symmetric_counit_left V (tensor_inj v w))).
rewrite paired_tensorE symmetric_coefficient_formE symmetric_counit_leftE (bilZl hmu) hu.
exact (esym (linZ (hom_linear a) (symmetric_augmentation V v : K) w)).
Qed.
(** Source for [symmetric_coefficient_right_unit_tensor]: Federer 1.10.2, p. 45,
    sentence asserting inheritance of a unit. In words: Supporting counit calculation when the coefficient is a right unit. *)
Lemma symmetric_coefficient_right_unit_tensor : right_id u mu -> forall (a : Hom E W) x,
  paired_tensor hmu a U x = a (symmetric_counit_right V x).
Proof.
move=> hu a x; apply: (tensor_ext (tensor_exists E E) (paired_tensor hmu a U)
  (linear_comp (hom_as_linear a) (symmetric_counit_right V))) x => v w.
change (paired_tensor hmu a U (tensor_inj v w) = a (symmetric_counit_right V (tensor_inj v w))).
rewrite paired_tensorE symmetric_coefficient_formE symmetric_counit_rightE (bilZr hmu) hu.
exact (esym (linZ (hom_linear a) (symmetric_augmentation V w : K) v)).
Qed.
(** Source for [symmetric_forms_unit_left]: Federer 1.10.2, p. 45,
    sentence asserting inheritance of a unit. In words: A left unit in the coefficient algebra gives a left unit for symmetric forms. *)
Theorem symmetric_forms_unit_left : left_id u mu -> left_id U (symmetric_forms_product hmu).
Proof.
move=> hu a; apply: hom_finite_ext => x.
by rewrite symmetric_forms_productE (symmetric_coefficient_left_unit_tensor hu) symmetric_counit_left_symmetric_diagonal.
Qed.
(** Source for [symmetric_forms_unit_right]: Federer 1.10.2, p. 45,
    sentence asserting inheritance of a unit. In words: A right unit in the coefficient algebra gives a right unit for symmetric forms. *)
Theorem symmetric_forms_unit_right : right_id u mu -> right_id U (symmetric_forms_product hmu).
Proof.
move=> hu a; apply: hom_finite_ext => x.
by rewrite symmetric_forms_productE (symmetric_coefficient_right_unit_tensor hu) symmetric_counit_right_symmetric_diagonal.
Qed.
End Unit.

Section UnitalAlgebra.
Variable K : fieldType.
Variable V : lmodType K.
Variable W : algebra K.
(** Source for [symmetric_forms_unital_algebra]: Federer 1.10.2, p. 45,
    sentence asserting inheritance of a unit. In words: Package the resulting unital associative algebra when the coefficient algebra has those properties. *)
Definition symmetric_forms_unital_algebra : algebra K :=
  @Algebra K (S_star V W) (symmetric_forms_product (alg_bilinear W))
    (symmetric_coefficient_form V (alg_one W))
    (@symmetric_forms_product_bilinear K V W (alg_mul W) (alg_bilinear W))
    (@symmetric_forms_product_associative K V W (alg_mul W) (alg_bilinear W) (@alg_assoc K W))
    (@symmetric_forms_unit_left K V W (alg_mul W) (alg_bilinear W) (alg_one W) (@alg_unitl K W))
    (@symmetric_forms_unit_right K V W (alg_mul W) (alg_bilinear W) (alg_one W) (@alg_unitr K W)).
(** Source for [symmetric_forms_unital]: Federer 1.10.2, p. 45,
    sentence asserting inheritance of a unit. In words: Package its grading and graded multiplication. *)
Definition symmetric_forms_unital : unital_graded_algebra K :=
  @UnitalGradedAlgebra K symmetric_forms_unital_algebra (S_star_grading V W)
    (@symmetric_forms_product_graded K V W (alg_mul W) (alg_bilinear W)).
End UnitalAlgebra.

(** Source for [S_star_dual_coefficient]: Federer 1.10.2, p. 45, induced
    algebra maps. Pullback preserves coefficients, hence preserves a
    coefficient unit. *)
Lemma S_star_dual_coefficient (K : fieldType) (V V' W : lmodType K)
    (f : {linear V -> V'}) (w : W) :
  S_star_dual f (symmetric_coefficient_form V' w) = symmetric_coefficient_form V w.
Proof.
rewrite /symmetric_coefficient_form S_star_dual_include.
congr (sform_include _); apply: sform_ext=> t.
by rewrite S_m_dualE !zero_sformE.
Qed.
