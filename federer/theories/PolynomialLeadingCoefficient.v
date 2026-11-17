(** Federer (1969), 3.4.7, p. 325: actual leading
    coefficients supporting field polynomial division and Gauss's lemma. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialBasicLaws
  CommutativePolynomialDegreeUP NaturalConvolution NaturalConvolutionDegree.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Leading.
Variables A B:comNzRingType.
Variable embed:{rmorphism A->B}.
Variable variable:B.
Variable coefficient:B->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.

(** Source for [polynomial_product_leading_coefficient]: the
    leading product coefficient is the product of the
    actual leading coefficients, supporting 3.4.7, p. 325. *)
Lemma polynomial_product_leading_coefficient (P Q:B) m n:
  (forall i,(m<i)%N ->coefficient P i = 0) ->
  (forall i,(n<i)%N ->coefficient Q i = 0) ->
  coefficient (P*Q) (m+n)%N = coefficient P m*coefficient Q n.
Proof.
move=>hPHigh hQHigh.
rewrite (@polynomial_coefficient_multiply A B embed variable coefficient hP).
transitivity (natural_coefficient_convolution (coefficient P) (coefficient Q) (m+n)%N).
  by rewrite /natural_coefficient_convolution big_mkord.
exact:natural_convolution_leading_coefficient hPHigh hQHigh.
Qed.

(** Source for [polynomial_monomial_degree]: a nonzero
    scalar monomial has its printed exponent as degree,
    supporting division in 3.4.7, p. 325. *)
Lemma polynomial_monomial_degree (a:A) n:
  a<>0 ->is_polynomial_degree coefficient (embed a*variable^+n) n.
Proof.
move=>ha;split;first by rewrite (@polynomial_monomial_coefficient A B embed variable coefficient hP) eqxx.
move=>i hi;rewrite (@polynomial_monomial_coefficient A B embed variable coefficient hP).
have hDifferent:(i==n) = false by apply/negP=>/eqP h;by rewrite h ltnn in hi.
by rewrite hDifferent.
Qed.
End Leading.
