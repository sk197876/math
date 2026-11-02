(** Federer (1969), 1.10.2, pp. 44-45: the algebra of symmetric forms with
    coefficients. Coefficient multiplication is merely bilinear until
    associativity or commutativity is explicitly assumed. No characteristic
    restriction is needed. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Graded UnitalGradedTensor TensorAssociator
  Hom HomogeneousHom BoundedHom HomogeneousSum HomFiniteFunctor Convolution
  GradedConvolution ConvolutionAssociativity ConvolutionNaturality
  SymmetricAlgebra SymmetricGrading SymmetricMaps SymmetricDirectSum
  SymmetricDiagonal SymmetricCoassociativity SymmetricForms SymmetricFormWords
  SymmetricFormExtension SymmetricFormIsomorphism SymmetricFormSum SymmetricFormDual.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section SymmetricFormProduct.
Variable K : fieldType.
Variables V W : lmodType K.
Variable mu : W -> W -> W.
Hypothesis hmu : bilinear mu.
Local Notation E := (symmetric_unital V).
Local Notation G := (symmetric_grading V).
Local Notation D := (symmetric_diagonal V).
Local Notation hD := (@symmetric_diagonal_graded K V).
(** Source for [symmetric_forms_product]: Federer 1.10.2, pp. 44-45,
    definition and algebra-law paragraphs. In words: Multiply graded symmetric forms by composing the diagonal, the tensor product of their linear maps and the coefficient multiplication. *)
Definition symmetric_forms_product (a b : S_star V W) : S_star V W := finite_convolution hmu hD a b.
(** Source for [symmetric_forms_productE]: Federer 1.10.2, pp. 44-45,
    definition and algebra-law paragraphs. In words: Evaluation of the product is the bilinear paired tensor map after the diagonal. *)
Lemma symmetric_forms_productE a b x : symmetric_forms_product a b x = paired_tensor hmu a b (D x).
Proof. by []. Qed.
(** Source for [symmetric_forms_product_composite]: Federer 1.10.2, pp. 44-45,
    definition and algebra-law paragraphs. In words: The product has exactly the displayed three-map factorisation. *)
Lemma symmetric_forms_product_composite a b x :
  symmetric_forms_product a b x = nu hmu (tensor_map (hom_as_linear a) (hom_as_linear b) (D x)).
Proof. exact: paired_tensor_factorisation. Qed.
(** Source for [symmetric_forms_product_bilinear]: Federer 1.10.2, pp. 44-45,
    definition and algebra-law paragraphs. In words: The symmetric product of forms is bilinear. *)
Lemma symmetric_forms_product_bilinear : bilinear symmetric_forms_product.
Proof. exact: finite_convolution_bilinear. Qed.
(** Source for [symmetric_forms_product_graded]: Federer 1.10.2, pp. 44-45,
    definition and algebra-law paragraphs. In words: Multiplication adds the degrees of homogeneous forms. *)
Lemma symmetric_forms_product_graded : graded_product (S_star_grading V W) symmetric_forms_product.
Proof. exact: finite_convolution_graded. Qed.
(** Source for [symmetric_forms_algebra]: Federer 1.10.2, pp. 44-45,
    definition and algebra-law paragraphs. In words: The resulting graded algebra, allowing a nonassociative coefficient multiplication. *)
Definition symmetric_forms_algebra : graded_algebra K :=
  @GradedAlgebra K (S_star V W) (S_star_grading V W) symmetric_forms_product
    symmetric_forms_product_bilinear symmetric_forms_product_graded.

(** Source for [sform_product]: Federer 1.10.2, pp. 44-45,
    definition and algebra-law paragraphs. In words: The product of a p-form and a q-form is a symmetric (p+q)-form. *)
Definition sform_product p q (a : S_m V W p) (b : S_m V W q) : S_m V W (p+q) :=
  homogeneous_sform (homogeneous_convolution hmu hD (sform_homogeneous a) (sform_homogeneous b)).
(** Source for [sform_product_include]: Federer 1.10.2, pp. 44-45,
    definition and algebra-law paragraphs. In words: The degree-wise product agrees with multiplication in the direct sum. *)
Lemma sform_product_include p q (a : S_m V W p) (b : S_m V W q) :
  sform_include (sform_product a b) = symmetric_forms_product (sform_include a) (sform_include b).
Proof.
rewrite /sform_product /sform_include homogeneous_sformK /symmetric_forms_product.
exact (esym (@finite_convolution_include K E W G mu hmu D hD p q
  (sform_homogeneous a) (sform_homogeneous b))).
Qed.
(** Source for [sform_productE]: Federer 1.10.2, pp. 44-45,
    definition and algebra-law paragraphs. In words: The actual tuple value is evaluation of the paired homogeneous maps after the diagonal. *)
Lemma sform_productE p q (a : S_m V W p) (b : S_m V W q) (t : (p+q).-tuple V) :
  sform_product a b t = paired_tensor hmu (sform_homogeneous a) (sform_homogeneous b) (D (symmetric_word t)).
Proof. by []. Qed.
(** Source for [sform_product_bilinear]: Federer 1.10.2, pp. 44-45,
    definition and algebra-law paragraphs. In words: The product is bilinear in each fixed pair of degrees. *)
Lemma sform_product_bilinear p q : bilinear (@sform_product p q).
Proof.
split.
- move=> b c a a'; apply: (can_inj (@sform_includeK K V W (p+q))).
  rewrite linearP !sform_product_include !linearP.
  change (symmetric_forms_product (c *: sform_include a + sform_include a') (sform_include b) =
    c *: sform_include (sform_product a b) + sform_include (sform_product a' b)).
  rewrite !sform_product_include; exact: (proj1 symmetric_forms_product_bilinear).
- move=> a c b b'; apply: (can_inj (@sform_includeK K V W (p+q))).
  rewrite linearP !sform_product_include !linearP.
  change (symmetric_forms_product (sform_include a) (c *: sform_include b + sform_include b') =
    c *: sform_include (sform_product a b) + sform_include (sform_product a b')).
  rewrite !sform_product_include; exact: (proj2 symmetric_forms_product_bilinear).
Qed.

(** Source for [symmetric_forms_diagonal_coassociative]: Federer 1.10.2, pp. 44-45,
    definition and algebra-law paragraphs. In words: Supporting form of coassociativity, with the tensor associator explicit. *)
Lemma symmetric_forms_diagonal_coassociative x :
  tensor_associator E E E (tensor_map D (linear_id E) (D x)) =
    tensor_map (linear_id E) D (D x).
Proof. exact: symmetric_diagonal_coassociative. Qed.
(** Source for [symmetric_forms_product_associative]: Federer 1.10.2, pp. 44-45,
    definition and algebra-law paragraphs. In words: Associativity of the coefficient multiplication implies associativity of the symmetric-form multiplication. *)
Theorem symmetric_forms_product_associative : associative mu -> associative symmetric_forms_product.
Proof.
move=> hA a b c; apply: val_inj.
exact (@convolution_associative K E W mu hmu hA D symmetric_forms_diagonal_coassociative a b c).
Qed.
(** Source for [symmetric_paired_tensor_swap]: Federer 1.10.2, pp. 44-45,
    definition and algebra-law paragraphs. In words: Supporting interchange identity: commutativity of coefficients exchanges the two tensor arguments without a sign. *)
Lemma symmetric_paired_tensor_swap (hC : commutative mu) (a b : Hom E W) x :
  paired_tensor hmu a b (graded_swap G G false x) = paired_tensor hmu b a x.
Proof.
elim/(tensor_homogeneous_induction (GA:=G) (GB:=G)): x =>
  [|x y hx hy|c x hx|r s x y hx hy].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
- rewrite (graded_swapE false hx hy).
  change (paired_tensor hmu a b ((1 : K) *: tensor_inj y x) =
    paired_tensor hmu b a (tensor_inj x y)).
  by rewrite scale1r !paired_tensorE hC.
Qed.

(** Source for [symmetric_forms_product_commutative]: Federer 1.10.2, pp. 44-45,
    definition and algebra-law paragraphs. In words: Commutativity of coefficient multiplication implies commutativity of the full symmetric-form algebra. *)
Theorem symmetric_forms_product_commutative : commutative mu -> commutative symmetric_forms_product.
Proof.
move=> hC a b; apply: hom_finite_ext=> x.
rewrite !symmetric_forms_productE.
have hd : graded_swap G G false (D x) = D x := @symmetric_diagonal_commutative K V x.
rewrite -{1}hd; exact: symmetric_paired_tensor_swap.
Qed.
End SymmetricFormProduct.

Section Naturality.
Variable K : fieldType.
Variables V V' W : lmodType K.
Variable mu : W -> W -> W.
Hypothesis hmu : bilinear mu.
Variable f : {linear V -> V'}.
(** Source for [S_star_dual_multiplicative]: Federer 1.10.2, pp. 44-45,
    definition and algebra-law paragraphs. In words: Every induced dual map is an algebra homomorphism: pullback preserves products. *)
Theorem S_star_dual_multiplicative (a b : S_star V' W) :
  S_star_dual f (symmetric_forms_product hmu a b) =
    symmetric_forms_product hmu (S_star_dual f a) (S_star_dual f b).
Proof.
apply: val_inj.
exact (@convolution_natural K (symmetric_space V) (symmetric_space V') W mu hmu
  (symmetric_algebra_map f) (symmetric_diagonal V) (symmetric_diagonal V') (@symmetric_diagonal_natural K V V' f) a b).
Qed.
End Naturality.
