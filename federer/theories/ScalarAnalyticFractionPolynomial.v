(** Federer (1969), 3.1.24, p. 239: evaluations
    of the scalar derivative forms in the composition sum. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import Hom HomogeneousHom SymmetricForms SymmetricFormWords SymmetricFormExtension
  SymmetricFunctionalProduct SymmetricAlgebra SymmetricMultiIndices SymmetricMonomials
  SymmetricDividedMonomials HomogeneousPolynomialFunctions PolynomialDiagonalNorm ScalarAnalyticFraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_analytic_fraction_polynomial_unit]: the
    normalized jth differential coefficient of cx/(1-cx)
    at zero, evaluated on unit scalar arguments, is c^j
    for positive j, Federer 3.1.24, p. 239. *)
Lemma scalar_analytic_fraction_polynomial_unit (R:realType) (c:R) j :
  (1<=j)%N -> sform_polynomial_value (scalar_analytic_fraction_form c j) 1= c^+j.
Proof.
case:j=>[|j] hj; first by [].
rewrite sform_polynomial_diagonal_value /scalar_analytic_fraction_form sform_scaleE
  symmetric_functional_product_formE.
have hp:(\prod_(i<j.+1) (tnth [tuple (1:R^o) | _<j.+1] i))= 1.
  under eq_bigr do rewrite tnth_mktuple.
  by rewrite prodr_const expr1n.
rewrite hp.
change ((((j.+1)`!)%:R:R)^-1*((c^+j.+1*((j.+1)`!)%:R)*1)= c^+j.+1).
have hf:(((j.+1)`!)%:R:R)!=0 by rewrite pnatr_eq0 -lt0n fact_gt0.
field; exact hf.
Qed.

(** Source for [scalar_analytic_fraction_form_word]: supporting
    the coefficient-sum evaluation in Federer 3.1.24,
    p. 239. The jth derivative form evaluates on
    a scalar word as c^j j! times its product. *)
Lemma scalar_analytic_fraction_form_word (R:realType) (c:R) j (s:seq R^o) :
  (1<=j)%N -> size s=j ->
  sform_homogeneous (scalar_analytic_fraction_form c j) (symmetric_word s)=
    (c^+j*(j`!)%:R)*\prod_(x<-s) x.
Proof.
case:j=>[|j] hj hs; first by [].
pose t:j.+1.-tuple R^o:=Tuple (introT eqP hs).
change (sform_homogeneous (scalar_analytic_fraction_form c j.+1) (symmetric_word t)=
  (c^+j.+1*((j.+1)`!)%:R)*\prod_(x<-t) x).
rewrite sform_homogeneousE sform_extensionE sform_wordsE.
rewrite /scalar_analytic_fraction_form sform_scaleE symmetric_functional_product_formE.
change ((c^+j.+1*((j.+1)`!)%:R)*(\prod_(i<j.+1) tnth t i)=
  (c^+j.+1*((j.+1)`!)%:R)*(\prod_(x<-t) x)).
by rewrite big_tuple.
Qed.

(** Source for [scalar_analytic_fraction_form_monomial]: each
    term in the scalar special case of Federer 3.1.24,
    p. 239, contributes gamma^(sum alpha) (sum alpha)!
    times the inner scalar monomial. The ordinary degree
    is required positive, as follows from weight p>=1. *)
Lemma scalar_analytic_fraction_form_monomial (R:realType) (c:R) k
    (x:'I_k->R^o) (alpha:symmetric_multi_index k) :
  (1<=symmetric_multi_degree alpha)%N ->
  sform_homogeneous (scalar_analytic_fraction_form c (symmetric_multi_degree alpha))
    (symmetric_monomial x alpha)=
    (c^+(symmetric_multi_degree alpha)*(symmetric_multi_degree alpha)`!%:R)*
      symmetric_scalar_monomial x alpha.
Proof.
move=>hd.
rewrite /symmetric_monomial (scalar_analytic_fraction_form_word c hd (symmetric_monomial_word_size x alpha)).
congr (_*_).
rewrite /symmetric_monomial_word /symmetric_scalar_monomial -big_enum.
have hrep n y:(\prod_(z<-nseq n y) z:R)= y^+n.
  by elim:n=>[|n ih]; rewrite /= ?big_nil ?big_cons ?expr0 ?exprS ?ih.
elim:(enum 'I_k)=>[|i s ih]; first by rewrite /= !big_nil.
by rewrite /= big_cat big_cons hrep ih.
Qed.
