(** Federer (1969), 3.1.11, p. 222:
    the coefficient product used to derive the
    general Leibniz rule from the algebra of
    polynomial functions in 1.10.4, p. 46. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import TensorUP BoundedHom Bilinear Graded GradedBilinearConvolution SymmetricForms
  SymmetricFormSum SymmetricFormProduct SymmetricPolynomialEvaluation
  SymmetricPolynomialInjectivity SymmetricPolynomialProduct
  PolynomialFunctions PolynomialTaylorTransform PolynomialTaylor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section TaylorProducts.
Variable K : fieldType.
Hypothesis h0 : [pchar K] =i pred0.
Variables X Y : lmodType K.
Variable mu : Y->Y->Y.
Hypothesis hmu : bilinear mu.

(** Source for [symmetric_taylor_transform_product]:
    translating a pointwise polynomial product
    translates both factors, supporting the
    product-of-jets argument in Federer 3.1.11,
    p. 222. *)
Lemma symmetric_taylor_transform_product (a b : S_star X Y) x :
  symmetric_taylor_transform (symmetric_forms_product hmu a b) x=
    symmetric_forms_product hmu (symmetric_taylor_transform a x)
      (symmetric_taylor_transform b x).
Proof.
apply: (symmetric_polynomial_injective h0); apply: funext=>v.
by rewrite !(symmetric_taylor_transform_value h0)
  !(symmetric_polynomial_product_value h0) !(symmetric_taylor_transform_value h0).
Qed.

(** Source for [symmetric_product_component_convolution]:
    the product of symmetric forms has
    the degree convolution printed in the
    Leibniz formula, Federer 3.1.11,
    p. 222. Inclusion into
    the graded sum avoids changing the
    degrees by an implicit equality cast. *)
Lemma symmetric_product_component_convolution (a b : S_star X Y) n :
  sform_include (sform_component n (symmetric_forms_product hmu a b))=
    \sum_(j<n.+1) symmetric_forms_product hmu
      (sform_include (sform_component (n-j) a))
      (sform_include (sform_component j b)).
Proof.
rewrite sform_componentK.
under eq_bigr do rewrite !sform_componentK.
exact (@graded_bilinear_component_convolution K (S_star X Y) (S_star_grading X Y)
  (symmetric_forms_product hmu) (@symmetric_forms_product_bilinear K X Y mu hmu)
  (@symmetric_forms_product_graded K X Y mu hmu) n a b).
Qed.

(** Source for [polynomial_taylor_product_coefficients]:
    the degree-n coefficient of a product
    at a equals the convolution of the
    two Taylor coefficient families, used in
    Federer 3.1.11, p. 222. *)
Theorem polynomial_taylor_product_coefficients (P Q : PolynomialFunction X Y) a n :
  sform_include (polynomial_taylor_coefficient (polynomial_product hmu P Q) n a)=
    \sum_(j<n.+1) symmetric_forms_product hmu
      (sform_include (polynomial_taylor_coefficient P (n-j) a))
      (sform_include (polynomial_taylor_coefficient Q j a)).
Proof.
rewrite /polynomial_taylor_coefficient /polynomial_product
  (polynomial_from_formsK h0) symmetric_taylor_transform_product.
exact: symmetric_product_component_convolution.
Qed.
End TaylorProducts.
