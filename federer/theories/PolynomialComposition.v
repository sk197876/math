(** Federer (1969), 3.1.11, p. 222: the composition of
    the two jet polynomials is a polynomial. This algebraic supporting
    result uses the sealed symmetric algebra and the polynomial
    representation and product laws of 1.10.4, pp. 45–47.
    No finite-dimensionality is required. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import Hom TensorUP HomogeneousHom BoundedHom HomogeneousSum Bilinear SymmetricAlgebra SymmetricDividedMonomials
  SymmetricForms SymmetricFormZero SymmetricFormExtension SymmetricFormSum
  HomogeneousPolynomialFunctions PolynomialDiagonalNorm SymmetricPolynomialEvaluation
  PolynomialFunctions PolynomialRepresentations PolynomialLinearComposition
  SymmetricPolynomialProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [composition_polynomial_constant]: the degree-zero
    term in the polynomial composition used in Federer 3.1.11,
    p. 222; supporting instance of 1.10.4, p. 46. *)
Lemma composition_polynomial_constant (K : fieldType) (X Y : lmodType K) (y : Y) :
  is_polynomial_function (fun _ : X=>y).
Proof.
exists (sform_include (zero_sform X y))=>x.
rewrite symmetric_polynomial_value_include sform_polynomial_diagonal_value.
by rewrite zero_sformE fact0 invr1 scale1r.
Qed.

(** Source for [composition_polynomial_scale]: scalar multiples
    of the polynomial terms remain polynomial, supporting the
    factorial divisions in Federer 3.1.11, p. 222. *)
Lemma composition_polynomial_scale (K : fieldType) (X Y : lmodType K)
    (f : X->Y) (c : K) :
  is_polynomial_function f -> is_polynomial_function (fun x=>c*:f x).
Proof.
move=>[F hF]; exists (c*:F)=>x.
by rewrite linearZ /= hF.
Qed.

(** Source for [composition_polynomial_sum]: finite sums of
    polynomial terms remain polynomial, supporting the jet
    composition in Federer 3.1.11, p. 222. *)
Lemma composition_polynomial_sum (K : fieldType) (X Y : lmodType K)
    (I : finType) (f : I->X->Y) :
  (forall i, is_polynomial_function (f i)) ->
  is_polynomial_function (fun x=>\sum_i f i x).
Proof.
move=>hf.
have hex : forall i, exists F : S_star X Y, f i =1 symmetric_polynomial_value F.
  exact hf.
have [F hF] := choice hex.
exists (\sum_i F i)=>x.
have hv (g : I->X->Y) : (\sum_i g i) x=\sum_i g i x.
  by elim/big_rec2: _=>[|i y g0 _ <-].
rewrite linear_sum hv.
apply: eq_bigr=>i _; exact: hF.
Qed.

(** Source for [composition_polynomial_product]: the pointwise
    product rule of 1.10.4, p. 46, used to expand the powers
    in Federer 3.1.11, p. 222. Bilinearity suffices. *)
Lemma composition_polynomial_product (K : fieldType) (h0 : [pchar K]=i pred0)
    (X Y : lmodType K) (mu : Y->Y->Y) (hmu : bilinear mu) (f g : X->Y) :
  is_polynomial_function f -> is_polynomial_function g ->
  is_polynomial_function (fun x=>mu (f x) (g x)).
Proof.
move=>hf hg.
pose P := @PolynomialMap K X Y f (introT (asboolP _) hf).
pose Q := @PolynomialMap K X Y g (introT (asboolP _) hg).
pose F := @polynomial_product K X Y mu hmu P Q.
exists (polynomial_to_forms F)=>x.
rewrite -polynomial_from_formsE polynomial_to_formsK /F.
exact: esym (@polynomial_productE K h0 X Y mu hmu P Q x).
Qed.

(** Source for [polynomial_symmetric_vector_power]: the jth
    power of the first jet in the sealed symmetric algebra is
    polynomial, supporting Federer 3.1.11, p. 222. The
    empty power is the algebra unit. *)
Theorem polynomial_symmetric_vector_power (K : fieldType) (h0 : [pchar K]=i pred0)
    (X Y : lmodType K) (f : X->Y) n :
  is_polynomial_function f ->
  is_polynomial_function (fun x=>symmetric_vector_power (f x) n).
Proof.
move=>hf; elim:n=>[|n ih].
- change (is_polynomial_function (fun _ : X=>@symmetric_unit K Y)).
  exact: composition_polynomial_constant.
have hg := polynomial_linear_postcompose
  (GRing.Linear.clone _ _ _ _ (@symmetric_generator K Y) _) hf.
have hp := composition_polynomial_product h0 (@symmetric_product_bilinear K Y) hg ih.
have he : (fun x=>symmetric_vector_power (f x) n.+1)=
    (fun x=>symmetric_product (symmetric_generator (f x))
      (symmetric_vector_power (f x) n)).
  apply: funext=>x; rewrite /symmetric_vector_power /= symmetric_word_cons.
  reflexivity.
by rewrite he.
Qed.

(** Source for [polynomial_function_composition]: Q composed
    with P is a polynomial, as used for the jet calculation in
    Federer 3.1.11, p. 222. This assertion is purely algebraic;
    continuity conditions belong to the subsequent calculus theorem. *)
Theorem polynomial_function_composition (K : fieldType) (h0 : [pchar K]=i pred0)
    (X Y Z : lmodType K) (f : X->Y) (g : Y->Z) :
  is_polynomial_function f -> is_polynomial_function g ->
  is_polynomial_function (fun x=>g (f x)).
Proof.
move=>hf /polynomial_finite_representation [N [phi hphi]].
have hterm i : is_polynomial_function (fun x=>sform_polynomial_value (phi i) (f x)).
  have hp := polynomial_symmetric_vector_power h0 i hf.
  have hd := composition_polynomial_scale (((i`!)%:R : K)^-1) hp.
  have hh := polynomial_linear_postcompose (hom_as_linear (sform_homogeneous (phi i))) hd.
  exact hh.
have hs := @composition_polynomial_sum K X Z 'I_N
  (fun i x=>sform_polynomial_value (phi i) (f x)) (fun i=>hterm i).
have he : (fun x=>g (f x))=(fun x=>\sum_(i<N) sform_polynomial_value (phi i) (f x)).
  apply: funext=>x; exact: hphi.
by rewrite he.
Qed.
