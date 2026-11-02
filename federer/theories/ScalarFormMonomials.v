(** Federer (1969), 3.1.11, p. 223: the scalar
    symmetric-form products appearing in the reciprocal formula. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Hom HomogeneousHom BoundedHom Bilinear
  AlgebraUP GradedAlgebra ScalarCoefficients SymmetricForms SymmetricFormSum
  SymmetricFormZero SymmetricFormProduct SymmetricFormUnit HomogeneousPolynomialFunctions
  PolynomialDiagonalNorm SymmetricPolynomialEvaluation SymmetricPolynomialProduct
  SymmetricMultiIndices SymmetricMonomials SymmetricDividedMonomials
  CompositionMultiIndices CompositionFormMonomials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_monomial_common_scale]: multiplying
    every factor by c multiplies a monomial by c to the
    total degree, used for the factors -1/f(a) in Federer
    3.1.11, p. 223. *)
Lemma scalar_monomial_common_scale (K : fieldType) k
    (x : 'I_k->K) (a : symmetric_multi_index k) c :
  symmetric_scalar_monomial (fun i=>c*x i) a=
    c^+(symmetric_multi_degree a)*symmetric_scalar_monomial x a.
Proof.
rewrite /symmetric_scalar_monomial /symmetric_multi_degree.
under eq_bigr do rewrite exprMn.
by rewrite big_split -expr_sum.
Qed.

Section ScalarFormMonomials.
Variable K : fieldType.
Variable X : lmodType K.
Variable k : nat.
Variable phi : forall i, S_m X K^o i.
Local Notation M := (scalar_bilinear K).
Local Notation G := (S_star_grading X K^o).

(** Source for [scalar_form_word]: the ordered symmetric
    product of scalar derivative forms, Federer 3.1.11,
    p. 223; the empty word has value one. *)
Fixpoint scalar_form_word (s : seq 'I_k) : S_star X K^o :=
  if s is i::s' then symmetric_forms_product M (sform_include (phi (val i).+1))
    (scalar_form_word s') else symmetric_coefficient_form X (1:K^o).

(** Source for [scalar_form_word_homogeneous]: the degree
    of a product is the sum of its factor degrees, supporting
    the reciprocal formula in Federer 3.1.11, p. 223. *)
Lemma scalar_form_word_homogeneous s :
  homogeneous G (\sum_(i <- s) (val i).+1)%N (scalar_form_word s).
Proof.
elim:s=>[|i s ih]; rewrite /= ?big_nil ?big_cons.
- exact: symmetric_coefficient_form_homogeneous.
- apply: (@symmetric_forms_product_graded K X K^o (fun x y=>x*y) M).
  + exact: sform_include_homogeneous.
  + exact ih.
Qed.

(** Source for [scalar_form_word_value]: divided-power
    evaluation sends the symmetric product to the ordinary product
    of scalar polynomial values, Federer 3.1.11, p. 223. *)
Lemma scalar_form_word_value (h0 : [pchar K]=i pred0) s v :
  symmetric_polynomial_value (scalar_form_word s) v=
    \prod_(i <- s) sform_polynomial_value (phi (val i).+1) v.
Proof.
elim:s=>[|i s ih].
- rewrite /= big_nil /symmetric_coefficient_form symmetric_polynomial_value_include
    sform_polynomial_diagonal_value zero_sformE fact0 invr1 scale1r.
  reflexivity.
- by rewrite /= big_cons (symmetric_polynomial_product_value h0) ih
    symmetric_polynomial_value_include.
Qed.

(** Source for [scalar_form_monomial]: the product
    (D^1 f)^alpha_1 ... (D^k f)^alpha_k in the scalar
    symmetric-form algebra, Federer 3.1.11, p. 223. *)
Definition scalar_form_monomial (a : symmetric_multi_index k) : S_star X K^o :=
  scalar_form_word (symmetric_monomial_word (fun i : 'I_k=>i) a).

(** Source for [scalar_form_monomial_homogeneous]: a monomial
    of the derivative forms has its weighted degree, Federer
    3.1.11, p. 223. *)
Lemma scalar_form_monomial_homogeneous a :
  homogeneous G (composition_multi_weight a) (scalar_form_monomial a).
Proof. rewrite -composition_weighted_word_degree; exact: scalar_form_word_homogeneous. Qed.

(** Source for [scalar_form_monomial_value]: the homogeneous
    polynomial of a monomial is the product of the individual
    polynomial powers, Federer 3.1.11, p. 223. *)
Lemma scalar_form_monomial_value (h0 : [pchar K]=i pred0) a v :
  symmetric_polynomial_value (scalar_form_monomial a) v=
    symmetric_scalar_monomial (fun i : 'I_k=>sform_polynomial_value (phi (val i).+1) v) a.
Proof.
rewrite /scalar_form_monomial scalar_form_word_value //
  /symmetric_monomial_word /symmetric_scalar_monomial -big_enum.
have hrep n (i : 'I_k) :
    \prod_(j <- nseq n i) sform_polynomial_value (phi (val j).+1) v=
      (sform_polynomial_value (phi (val i).+1) v)^+n.
  by elim:n=>[|n ih]; rewrite /= ?big_nil ?big_cons ?expr0 ?exprS ?ih.
elim:(enum 'I_k)=>[|i s ih]; first by rewrite /= !big_nil.
by rewrite /= big_cat big_cons hrep ih.
Qed.

(** Source for [scalar_form_monomial_component_value]: at
    the weighted degree p, the pth homogeneous component gives
    the same product of polynomial values, Federer 3.1.11, p. 223. *)
Lemma scalar_form_monomial_component_value (h0 : [pchar K]=i pred0) a p v :
  composition_multi_weight a=p ->
  sform_polynomial_value (sform_component p (scalar_form_monomial a)) v=
    symmetric_scalar_monomial (fun i : 'I_k=>sform_polynomial_value (phi (val i).+1) v) a.
Proof.
move=>hp; have hh := scalar_form_monomial_homogeneous a.
rewrite hp /homogeneous in hh.
rewrite -symmetric_polynomial_value_include sform_componentK hh.
exact: scalar_form_monomial_value.
Qed.
End ScalarFormMonomials.
