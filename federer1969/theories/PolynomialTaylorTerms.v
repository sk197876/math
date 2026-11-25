(** Federer (1969), 1.10.4, p. 46, Taylor's formula and the displayed
    contraction coefficients. This module proves the expansion of each
    homogeneous term before collecting equal degrees. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import TensorUP Bilinear Graded GradedSums GradedComponents
  Hom HomogeneousHom BoundedHom HomogeneousSum SymmetricAlgebra
  SymmetricGrading SymmetricDividedMonomials SymmetricMultinomial
  SymmetricForms SymmetricFormWords SymmetricFormExtension SymmetricFormIsomorphism SymmetricFormSum
  SymmetricFiniteContraction HomogeneousPolynomialFunctions
  SymmetricPolynomialEvaluation PolynomialFunctions PolynomialRepresentations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section TaylorTerms.
Variable K : fieldType.
Variables V W : lmodType K.
Local Notation G := (symmetric_grading V).

(** Source for [symmetric_divided_power_homogeneous]: Federer
    1.10.4, p. 46, supporting degree of x^r/r! in the
    displayed contraction definition. *)
Lemma symmetric_divided_power_homogeneous (x : V) r :
  homogeneous G r (symmetric_divided_vector_power x r).
Proof. apply: homogeneousZ; exact: symmetric_vector_power_homogeneous. Qed.

(** Source for [symmetric_divided_power_component]: Federer
    1.10.4, p. 46, x^r/r! regarded as an element of the
    actual homogeneous power space for the contraction operation. *)
Definition symmetric_divided_power_component (x : V) r : symmetric_power V r :=
  @Component K (symmetric_space V) G r (symmetric_divided_vector_power x r)
    (introT eqP (symmetric_divided_power_homogeneous x r)).

(** Source for [symmetric_taylor_term]: Federer 1.10.4,
    p. 46, the degree-i form obtained by contracting the
    degree-m coefficient with x^(m-i)/(m-i)!. Taking the component
    also makes the formula zero for i>m. *)
Definition symmetric_taylor_term m i (f : S_m V W m) (x : V) : S_m V W i :=
  sform_component i (symmetric_finite_contraction
    (symmetric_divided_power_component x (m-i)) (sform_include f)).

(** Source for [symmetric_taylor_term_pairing]: Federer
    1.10.4, p. 46, the characteristic pairing of each
    contraction term against an i-vector. *)
Lemma symmetric_taylor_term_pairing m i (f : S_m V W m) x xi :
  homogeneous G i xi ->
  sform_homogeneous (symmetric_taylor_term i f x) xi =
    sform_homogeneous f (symmetric_product xi (symmetric_divided_vector_power x (m-i))).
Proof.
move=> hxi; rewrite /symmetric_taylor_term /sform_component homogeneous_sformK
  homogeneous_pieceE.
change (symmetric_finite_contraction (symmetric_divided_power_component x (m-i))
  (sform_include f) (grade G i xi) =
  sform_homogeneous f (symmetric_product xi (symmetric_divided_vector_power x (m-i)))).
rewrite hxi symmetric_finite_contractionE; by [].
Qed.

(** Source for [symmetric_taylor_term_value]: Federer
    1.10.4, p. 46, evaluating the coefficient against v^i/i!
    gives the mixed divided-power product in the double sum. *)
Lemma symmetric_taylor_term_value m i (f : S_m V W m) x v :
  sform_polynomial_value (symmetric_taylor_term i f x) v =
    sform_homogeneous f (symmetric_product (symmetric_divided_vector_power v i)
      (symmetric_divided_vector_power x (m-i))).
Proof. apply: symmetric_taylor_term_pairing; exact: symmetric_divided_power_homogeneous. Qed.

(** Source for [symmetric_taylor_term_above_degree]: Federer
    1.10.4, p. 46, the lower index m=i in the coefficient
    sum. Terms with original degree m<i vanish by homogeneity. *)
Lemma symmetric_taylor_term_above_degree m i (f : S_m V W m) x :
  (m<i)%N -> symmetric_taylor_term i f x = 0.
Proof.
move=> hmi; apply: sform_ext=> t; rewrite sform_zeroE.
rewrite -sform_wordsE -(sform_extensionE _).
change (sform_homogeneous (symmetric_taylor_term i f x) (symmetric_word t) = 0).
have ht : homogeneous G i (symmetric_word t).
  have h := symmetric_word_homogeneous t; by rewrite size_tuple in h.
rewrite (symmetric_taylor_term_pairing _ _ ht).
have hdegree : (i+(m-i))%N != m.
  have hle : (m<=i)%N := ltnW hmi.
  have hs : (m-i)%N=0%N by apply/eqP; rewrite subn_eq0.
  by rewrite hs addn0 neq_ltn hmi orbT.
apply: (hom_m_degree (sform_homogeneous f) hdegree).
exact: symmetric_product_graded ht (symmetric_divided_power_homogeneous x (m-i)).
Qed.

(** Source for [homogeneous_polynomial_taylor]: Federer
    1.10.4, p. 46, the inner sum of Taylor's formula for
    one homogeneous coefficient. It follows from the divided binomial
    formula, including m=0. *)
Theorem homogeneous_polynomial_taylor (h0 : [pchar K] =i pred0)
    m (f : S_m V W m) x v :
  sform_polynomial_value f (x+v) =
    \sum_(i < m.+1) sform_polynomial_value (symmetric_taylor_term i f x) v.
Proof.
rewrite /sform_polynomial_value addrC (symmetric_divided_binomial h0) linear_sum.
apply: eq_bigr=> i _; exact: esym (@symmetric_taylor_term_value m i f x v).
Qed.

(** Source for [polynomial_taylor_double_sum]: Federer
    1.10.4, p. 46, the first displayed Taylor equality as
    a double sum over the original degree and contraction degree. *)
Theorem polynomial_taylor_double_sum (h0 : [pchar K] =i pred0)
    (P : PolynomialFunction V W) x v :
  P (x+v) = \sum_(m < (polynomial_degree P).+1) \sum_(i < m.+1)
    sform_polynomial_value (symmetric_taylor_term i
      (sform_component m (polynomial_to_forms P)) x) v.
Proof.
rewrite polynomial_degree_representation.
apply: eq_bigr=> m _; exact: homogeneous_polynomial_taylor.
Qed.
End TaylorTerms.
