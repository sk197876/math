(** Federer (1969), 3.4.7, p. 325: the independent
    coefficient and evaluation equations determine every finite
    substitution and its uniqueness. These proofs do not
    inspect the private evaluation construction. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialFiniteSums
  CommutativePolynomialEvaluationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [polynomial_evaluation_finite_expression]: every
    actual polynomial evaluates to its finite original
    coefficient expression, supporting the transverse subring
    of 3.4.7, p. 325. *)
Theorem polynomial_evaluation_finite_expression (A B C:comNzRingType)
    (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
    (hP:is_commutative_polynomial_ring embed variable coefficient)
    (phi:{rmorphism A->C}) (t:C) (E:{rmorphism B->C})
    (hE:is_commutative_polynomial_evaluation embed variable phi t E) (P:B) N:
  (forall i,(N<=i)%N ->coefficient P i = 0) ->
  E P = \sum_(i<N) phi (coefficient P i)*t^+i.
Proof.
move=>hBound.
have hExpression:=@polynomial_finite_expression A B embed variable coefficient hP P N hBound.
rewrite {1}hExpression rmorph_sum.
apply:eq_bigr=>i _.
by rewrite rmorphM rmorphXn
  (@polynomial_evaluation_constants A B C embed variable phi t E hE)
  (@polynomial_evaluation_variable A B C embed variable phi t E hE).
Qed.

(** Source for [polynomial_evaluation_unique]: the original
    coefficient embedding and variable value determine evaluation
    uniquely, supporting the simple transcendental extension
    in 3.4.7, p. 325. *)
Theorem polynomial_evaluation_unique (A B C:comNzRingType)
    (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
    (hP:is_commutative_polynomial_ring embed variable coefficient)
    (phi:{rmorphism A->C}) (t:C) (E F:{rmorphism B->C}):
  is_commutative_polynomial_evaluation embed variable phi t E ->
  is_commutative_polynomial_evaluation embed variable phi t F ->
  forall P:B,E P = F P.
Proof.
move=>hE hF P.
have [N hN]:=@polynomial_coefficients_finite A B embed variable coefficient hP P.
by rewrite (@polynomial_evaluation_finite_expression A B C embed variable coefficient hP phi t E hE P N hN)
  (@polynomial_evaluation_finite_expression A B C embed variable coefficient hP phi t F hF P N hN).
Qed.
