(** Federer (1969), 1.10.4, p. 46: symmetric multiplication corresponds to
    pointwise multiplication of polynomial functions. The proof below
    selects the homogeneous term in the divided-power diagonal; this is
    equivalent to the printed shuffle-count cancellation. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp functions.
From Federer Require Import TensorUP Bilinear Graded GradedSums Hom HomogeneousHom
  BoundedHom Convolution GradedConvolution SymmetricAlgebra SymmetricGrading
  SymmetricDividedMonomials SymmetricDiagonal SymmetricDiagonalPowers
  SymmetricForms SymmetricFormExtension SymmetricFormIsomorphism SymmetricFormSum
  SymmetricFormProduct HomogeneousPolynomialFunctions SymmetricPolynomialEvaluation
  PolynomialFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Product.
Variable K : fieldType.
Hypothesis h0 : [pchar K] =i pred0.
Variables V W : lmodType K.
Variable mu : W -> W -> W.
Hypothesis hmu : bilinear mu.
Local Notation A := (S_star V W).

(** Source for [homogeneous_polynomial_product]: Federer 1.10.4,
    p. 46, the displayed multiplication identity for degrees p and q.
    Factorial normalization cancels the shuffle coefficient exactly. *)
Theorem homogeneous_polynomial_product p q (a : S_m V W p) (b : S_m V W q) x :
  sform_polynomial_value (sform_product hmu a b) x =
    mu (sform_polynomial_value a x) (sform_polynomial_value b x).
Proof.
rewrite /sform_polynomial_value /sform_product homogeneous_sformK.
change (paired_tensor hmu (sform_homogeneous a) (sform_homogeneous b)
  (symmetric_diagonal V (symmetric_divided_vector_power x (p+q))) =
  mu (sform_homogeneous a (symmetric_divided_vector_power x p))
    (sform_homogeneous b (symmetric_divided_vector_power x q))).
rewrite (symmetric_diagonal_divided_power h0) linear_sum.
under eq_bigr do rewrite paired_tensorE.
have hp : (p < (p+q).+1)%N by rewrite ltnS leq_addr.
pose ip : 'I_(p+q).+1 := Ordinal hp.
rewrite (bigD1 ip) //= addKn.
have hz : (\sum_(i : 'I_(p+q).+1 | i != ip)
  mu (sform_homogeneous a (symmetric_divided_vector_power x i))
    (sform_homogeneous b (symmetric_divided_vector_power x (p+q-i)))) = 0.
  apply: big1=> i hi.
  have hip : val i != p by move: hi; rewrite -val_eqE.
  have hx : homogeneous (symmetric_grading V) i (symmetric_divided_vector_power x i).
    apply: homogeneousZ; exact: symmetric_vector_power_homogeneous.
  rewrite (hom_m_degree (sform_homogeneous a) hip hx).
  exact: (@bil0l K W W W mu hmu).
by rewrite hz addr0.
Qed.

(** Source for [symmetric_polynomial_product_value]: Federer
    1.10.4, p. 46, the full graded-form product is mapped to
    pointwise coefficient multiplication. Bilinearity alone suffices here. *)
Theorem symmetric_polynomial_product_value (a b : A) x :
  symmetric_polynomial_value (symmetric_forms_product hmu a b) x =
    mu (symmetric_polynomial_value a x) (symmetric_polynomial_value b x).
Proof.
move: a b x; apply: symmetric_form_sum_induction.
- move=> b x; rewrite (bil0l (@symmetric_forms_product_bilinear K V W mu hmu))
    !linear0 /=; exact: esym (@bil0l K W W W mu hmu _).
- move=> a a' ha ha' b x.
  rewrite (bilDl (@symmetric_forms_product_bilinear K V W mu hmu)) !linearD.
  change (symmetric_polynomial_value (symmetric_forms_product hmu a b) x +
    symmetric_polynomial_value (symmetric_forms_product hmu a' b) x =
    mu (symmetric_polynomial_value a x + symmetric_polynomial_value a' x)
      (symmetric_polynomial_value b x)).
  rewrite ha ha'.
  exact: esym (@bilDl K W W W mu hmu _ _ _).
- move=> p a; apply: symmetric_form_sum_induction.
  + move=> x; rewrite (bil0r (@symmetric_forms_product_bilinear K V W mu hmu))
      !linear0 /=; exact: esym (@bil0r K W W W mu hmu _).
  + move=> b b' hb hb' x.
    rewrite (bilDr (@symmetric_forms_product_bilinear K V W mu hmu)) !linearD.
    change (symmetric_polynomial_value (symmetric_forms_product hmu (sform_include a) b) x +
      symmetric_polynomial_value (symmetric_forms_product hmu (sform_include a) b') x =
      mu (symmetric_polynomial_value (sform_include a) x)
        (symmetric_polynomial_value b x + symmetric_polynomial_value b' x)).
    rewrite hb hb'.
    exact: esym (@bilDr K W W W mu hmu _ _ _).
  + move=> q b x.
    rewrite -sform_product_include !symmetric_polynomial_value_include.
    exact: homogeneous_polynomial_product.
Qed.

(** Source for [polynomial_product]: Federer 1.10.4, p. 46,
    pointwise multiplication preserves the polynomial-function space;
    the form product supplies its representation. *)
Definition polynomial_product (P Q : PolynomialFunction V W) : PolynomialFunction V W :=
  polynomial_from_forms (symmetric_forms_product hmu (polynomial_to_forms P) (polynomial_to_forms Q)).

(** Source for [polynomial_productE]: Federer 1.10.4,
    p. 46, the product on polynomial functions is pointwise multiplication. *)
Lemma polynomial_productE P Q x : polynomial_product P Q x = mu (P x) (Q x).
Proof.
rewrite /polynomial_product polynomial_from_formsE symmetric_polynomial_product_value.
have hP := congr1 (fun F : PolynomialFunction V W => F x) (polynomial_to_formsK P).
have hQ := congr1 (fun F : PolynomialFunction V W => F x) (polynomial_to_formsK Q).
by rewrite -!polynomial_from_formsE hP hQ.
Qed.

(** Source for [polynomial_product_bilinear]: Federer 1.10.4,
    p. 46, the polynomial-function space is an algebra under the
    pointwise coefficient product. *)
Lemma polynomial_product_bilinear : bilinear polynomial_product.
Proof.
split.
- move=> Q a P P'; apply: polynomial_function_ext=> x.
  change (polynomial_product (a *: P+P') Q x =
    a *: polynomial_product P Q x + polynomial_product P' Q x).
  rewrite !polynomial_productE; exact: (proj1 hmu).
- move=> P a Q Q'; apply: polynomial_function_ext=> x.
  change (polynomial_product P (a *: Q+Q') x =
    a *: polynomial_product P Q x + polynomial_product P Q' x).
  rewrite !polynomial_productE; exact: (proj2 hmu).
Qed.

(** Source for [polynomial_from_forms_multiplicative]: Federer
    1.10.4, p. 46, the linear identification is an algebra
    isomorphism: it preserves the symmetric and pointwise products. *)
Theorem polynomial_from_forms_multiplicative a b :
  polynomial_from_forms (symmetric_forms_product hmu a b) =
    polynomial_product (polynomial_from_forms a) (polynomial_from_forms b).
Proof.
apply: polynomial_function_ext=> x.
by rewrite polynomial_productE !polynomial_from_formsE symmetric_polynomial_product_value.
Qed.
End Product.
