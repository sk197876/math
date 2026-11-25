(** Federer (1969), 3.4.7, p. 325: polynomial
    evaluation hidden behind its proved coefficient and variable
    equations. Finite support choices remain private. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialEvaluationUP PolynomialSubstitutionArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type CommutativePolynomialEvaluationSignature.
(** Source for [map]: the polynomial homomorphism extending
    the original coefficients and variable value, supporting
    3.4.7, p. 325. *)
Parameter map:forall (A B C:comNzRingType) (embed:{rmorphism A->B})
  (variable:B) (coefficient:B->nat->A),
  is_commutative_polynomial_ring embed variable coefficient ->
  {rmorphism A->C}->C->{rmorphism B->C}.
(** Source for [laws]: the independent evaluation equations
    supporting the original subring in 3.4.7, p. 325. *)
Parameter laws:forall (A B C:comNzRingType) (embed:{rmorphism A->B})
  (variable:B) (coefficient:B->nat->A)
  (hP:is_commutative_polynomial_ring embed variable coefficient) (phi:{rmorphism A->C}) (t:C),
  is_commutative_polynomial_evaluation embed variable phi t
    (@map A B C embed variable coefficient hP phi t).
End CommutativePolynomialEvaluationSignature.
Module CommutativePolynomialEvaluation:CommutativePolynomialEvaluationSignature.
(** Source for [map]: a hidden choice from proved
    homomorphism existence, supporting 3.4.7, p. 325. *)
Definition map (A B C:comNzRingType) (embed:{rmorphism A->B})
  (variable:B) (coefficient:B->nat->A)
  (hP:is_commutative_polynomial_ring embed variable coefficient) (phi:{rmorphism A->C}) (t:C):
    {rmorphism B->C}:=
  projT1 (cid (@commutative_polynomial_evaluation_exists A B C embed variable coefficient hP phi t)).
(** Source for [laws]: the hidden choice satisfies the
    independent original equations, supporting 3.4.7, p. 325. *)
Lemma laws (A B C:comNzRingType) (embed:{rmorphism A->B})
  (variable:B) (coefficient:B->nat->A)
  (hP:is_commutative_polynomial_ring embed variable coefficient) (phi:{rmorphism A->C}) (t:C):
  is_commutative_polynomial_evaluation embed variable phi t
    (@map A B C embed variable coefficient hP phi t).
Proof.
exact:(projT2 (cid (@commutative_polynomial_evaluation_exists A B C embed variable coefficient hP phi t))).
Qed.
End CommutativePolynomialEvaluation.
