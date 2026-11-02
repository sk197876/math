(** Federer (1969), 3.1.11, p. 222: the powers and
    products of D^i f(a) in the symmetric-form algebra with
    coefficients in the symmetric algebra of the intermediate space. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Hom HomogeneousHom BoundedHom Bilinear
  AlgebraUP GradedAlgebra SymmetricAlgebra SymmetricForms SymmetricFormPostcompose
  SymmetricFormSum SymmetricFormZero SymmetricFormProduct SymmetricFormUnit
  HomogeneousPolynomialFunctions PolynomialDiagonalNorm SymmetricPolynomialEvaluation
  SymmetricPolynomialProduct SymmetricMultiIndices SymmetricMonomials
  CompositionMultiIndices.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [composition_form_postcompose_value]: applying
    an outer linear map to a symmetric form commutes with its
    divided-power evaluation, Federer 3.1.11, p. 222. *)
Lemma composition_form_postcompose_value (K : fieldType)
    (X Y T : lmodType K) (L : {linear Y->T}) p (phi : S_m X Y p) v :
  sform_polynomial_value (symmetric_form_postcompose L phi) v=
    L (sform_polynomial_value phi v).
Proof. by rewrite !sform_polynomial_diagonal_value symmetric_form_postcomposeE linearZ. Qed.

(** Source for [composition_weighted_word_degree]: the word
    with alpha_i copies of i has total graded degree
    sum_i i alpha_i, Federer 3.1.11, p. 222. *)
Lemma composition_weighted_word_degree k (a : symmetric_multi_index k) :
  (\sum_(i <- symmetric_monomial_word (fun i : 'I_k=>i) a) (val i).+1)%N=
    composition_multi_weight a.
Proof.
rewrite /symmetric_monomial_word /composition_multi_weight -big_enum.
have hrepeat n (i : 'I_k) : (\sum_(j <- nseq n i) (val j).+1)%N=((val i).+1*n)%N.
  elim:n=>[|n ih]; first by rewrite big_nil muln0.
  by rewrite /= big_cons ih mulnS.
elim:(enum 'I_k)=>[|i s ih]; first by rewrite /= !big_nil.
by rewrite /= big_cat big_cons hrepeat ih.
Qed.

Section FormMonomials.
Variable K : fieldType.
Variables X Y : lmodType K.
Variable k : nat.
Variable phi : forall i, S_m X Y i.
Local Notation SY := (symmetric_space Y).
Local Notation M := (@symmetric_product_bilinear K Y).
Local Notation G := (S_star_grading X SY).

(** Source for [composition_inner_form]: the form D^i f(a)
    regarded as taking values in degree one of the symmetric
    algebra of Y, Federer 3.1.11, p. 222. *)
Definition composition_inner_form (i : 'I_k) : S_star X SY :=
  sform_include (symmetric_form_postcompose
    (GRing.Linear.clone _ _ _ _ (@symmetric_generator K Y) _) (phi (val i).+1)).

(** Source for [composition_form_word]: the ordered product
    in the symmetric-form algebra used for the displayed powers
    in Federer 3.1.11, p. 222; the empty word is the unit. *)
Fixpoint composition_form_word (s : seq 'I_k) : S_star X SY :=
  if s is i::s' then symmetric_forms_product M (composition_inner_form i)
    (composition_form_word s') else symmetric_coefficient_form X (symmetric_unit Y).

(** Source for [composition_form_word_homogeneous]: the degree
    of the product is the sum of its factor degrees, supporting
    the weighted grouping in Federer 3.1.11, p. 222. *)
Lemma composition_form_word_homogeneous s :
  homogeneous G (\sum_(i <- s) (val i).+1)%N (composition_form_word s).
Proof.
elim:s=>[|i s ih]; rewrite /= ?big_nil ?big_cons.
- exact: symmetric_coefficient_form_homogeneous.
- apply: (@symmetric_forms_product_graded K X SY (@symmetric_product K Y) M).
  + exact: sform_include_homogeneous.
  + exact ih.
Qed.

(** Source for [composition_form_word_value]: the polynomial
    value of the product is the symmetric word of the individual
    polynomial values, Federer 3.1.11, p. 222. *)
Lemma composition_form_word_value (h0 : [pchar K]=i pred0) s v :
  symmetric_polynomial_value (composition_form_word s) v=
    symmetric_word [seq sform_polynomial_value (phi (val i).+1) v | i <- s].
Proof.
elim:s=>[|i s ih].
- rewrite /= /symmetric_coefficient_form symmetric_polynomial_value_include
    sform_polynomial_diagonal_value zero_sformE fact0 invr1 scale1r.
  reflexivity.
- rewrite /= (symmetric_polynomial_product_value h0) ih
    /composition_inner_form symmetric_polynomial_value_include
    composition_form_postcompose_value symmetric_word_cons.
  reflexivity.
Qed.

(** Source for [composition_form_monomial]: the product
    (D^1 f)^alpha_1 ... (D^k f)^alpha_k in the symmetric-form
    algebra, Federer 3.1.11, p. 222. *)
Definition composition_form_monomial (a : symmetric_multi_index k) : S_star X SY :=
  composition_form_word (symmetric_monomial_word (fun i : 'I_k=>i) a).

(** Source for [composition_form_monomial_homogeneous]: the
    product indexed by alpha lies in its weighted degree,
    Federer 3.1.11, p. 222. *)
Lemma composition_form_monomial_homogeneous a :
  homogeneous G (composition_multi_weight a) (composition_form_monomial a).
Proof. rewrite -composition_weighted_word_degree; exact: composition_form_word_homogeneous. Qed.

(** Source for [composition_form_monomial_value]: evaluation
    of the inner product on a divided power gives the monomial
    of its divided-power values, Federer 3.1.11, p. 222. *)
Lemma composition_form_monomial_value (h0 : [pchar K]=i pred0) a v :
  symmetric_polynomial_value (composition_form_monomial a) v=
    symmetric_monomial (fun i : 'I_k=>sform_polynomial_value (phi (val i).+1) v) a.
Proof.
rewrite /composition_form_monomial composition_form_word_value //
  symmetric_monomial_word_map /symmetric_monomial.
reflexivity.
Qed.

(** Source for [composition_form_monomial_component_value]:
    at the weighted degree p, extracting the pth form leaves
    the same divided-power evaluation, Federer 3.1.11, p. 222. *)
Lemma composition_form_monomial_component_value (h0 : [pchar K]=i pred0) a p v :
  composition_multi_weight a=p ->
  sform_polynomial_value (sform_component p (composition_form_monomial a)) v=
    symmetric_monomial (fun i : 'I_k=>sform_polynomial_value (phi (val i).+1) v) a.
Proof.
move=>hp.
have hh := composition_form_monomial_homogeneous a.
rewrite hp /homogeneous in hh.
rewrite -symmetric_polynomial_value_include sform_componentK hh.
exact: composition_form_monomial_value.
Qed.
End FormMonomials.
