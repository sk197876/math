(** Federer (1969), 3.1.24, pp. 239–240: scalar
    evaluation of the exact composition coefficient, supporting
    the defining recurrence for inverse majorants. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom HomogeneousHom BoundedHom SymmetricAlgebra SymmetricForms SymmetricFormExtension
  SymmetricMultiIndices SymmetricIndexBounds SymmetricMonomials SymmetricDividedMonomials
  ScalarSymmetricFormEvaluation CompositionMultiIndices CompositionMultinomial
  CompositionFormCoefficient HomogeneousPolynomialFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_scalar_word_product]: supporting
    the scalar special cases in Federer 3.1.24, pp. 239–240.
    A word repeating x_i alpha_i times has scalar product
    equal to the monomial product_i x_i^alpha_i. *)
Lemma symmetric_scalar_word_product (K:fieldType) k (x:'I_k->K^o)
    (a:symmetric_multi_index k) :
  (\prod_(y<-symmetric_monomial_word x a) y)= symmetric_scalar_monomial x a.
Proof.
rewrite /symmetric_monomial_word /symmetric_scalar_monomial -big_enum.
have hrep n y:(\prod_(z<-nseq n y) z:K)= y^+n.
  by elim:n=>[|n ih]; rewrite /= ?big_nil ?big_cons ?expr0 ?exprS ?ih.
elim:(enum 'I_k)=>[|i s ih]; first by rewrite /= !big_nil.
by rewrite /= big_cat big_cons hrep ih.
Qed.

(** Source for [scalar_symmetric_form_monomial_evaluation]:
    a scalar monomial inserted in the outer derivative
    contributes its ordinary scalar monomial times the outer
    coefficient, supporting Federer 3.1.24, pp. 239–240. *)
Lemma scalar_symmetric_form_monomial_evaluation (K:fieldType) k (Y:lmodType K)
    (x:'I_k->K^o) (a:symmetric_multi_index k)
    (phi:S_m K^o Y (symmetric_multi_degree a)) :
  sform_homogeneous phi (symmetric_monomial x a)=
    symmetric_scalar_monomial x a*:phi [tuple (1:K^o) | i<symmetric_multi_degree a].
Proof.
rewrite /symmetric_monomial (scalar_symmetric_form_word_evaluation phi (symmetric_monomial_word_size x a)).
by rewrite symmetric_scalar_word_product.
Qed.

(** Source for [scalar_composition_coefficient_value]: the
    normalized scalar composition sum used in the inverse
    calculation in Federer 3.1.24, pp. 239–240. The
    inner coefficients are normalized polynomial values at one;
    the outer coefficient is its actual form value at a
    tuple of ones. No sign assumption is imposed. *)
Theorem scalar_composition_coefficient_value (K:fieldType) (h0:[pchar K]=i pred0)
    k (phi:forall i,S_m K^o K^o i) (psi:forall i,S_m K^o K^o i) p :
  (p<=k)%N ->
  sform_polynomial_value (@composition_differential_form_coefficient K K^o K^o K^o k phi psi p) 1=
    \sum_(a:composition_indices k p)
      ((symmetric_multi_factorial (composition_indices_unbound a))%:R)^-1*
      (symmetric_scalar_monomial
        (fun i:'I_k=>sform_polynomial_value (phi (val i).+1) 1) (composition_indices_unbound a))*
      psi (symmetric_multi_degree (composition_indices_unbound a))
        [tuple (1:K^o) | i<symmetric_multi_degree (composition_indices_unbound a)].
Proof.
move=>hp.
rewrite (@composition_differential_form_coefficient_value K K^o K^o K^o k phi psi h0 p 1 hp) composition_weight_coefficient_formula //.
apply:eq_bigr=>a _.
rewrite /composition_multinomial_term scalar_symmetric_form_monomial_evaluation.
pose A:K:=(symmetric_multi_factorial (composition_indices_unbound a))%:R^-1.
pose B:K:=symmetric_scalar_monomial
  (fun i:'I_k=>sform_polynomial_value (phi (val i).+1) 1) (composition_indices_unbound a).
pose C:K:=psi (symmetric_multi_degree (composition_indices_unbound a))
  [tuple (1:K^o) | i<symmetric_multi_degree (composition_indices_unbound a)].
change (A*(B*C)=(A*B)*C).
by rewrite mulrA.
Qed.
