(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: formal differentiation respects
    addition, scalar multiplication and a linear
    root factor. Reuse the existing coefficient
    arithmetic and variable-shift law. Source:
    Bourbaki, Algebra II (1990), Chapter IV,
    section 2, no. 2, pp. IV.17–18. *)
From mathcomp Require Import all_boot all_order all_algebra boolp ring.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialBasicLaws
  PolynomialCoefficientDivision FormalPolynomialDerivativeUP FormalPolynomialDerivativeExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Laws.
Variables A B:comNzRingType.
Variable embed:{rmorphism A->B}.
Variable variable:B.
Variable coefficient:B->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.

(** Source for [formal_polynomial_derivative_add]:
    addition in the cited formal differentiation laws. *)
Lemma formal_polynomial_derivative_add (P Q DP DQ:B):
  is_formal_polynomial_derivative coefficient P DP ->
  is_formal_polynomial_derivative coefficient Q DQ ->
  is_formal_polynomial_derivative coefficient (P+Q) (DP+DQ).
Proof.
move=>hDP hDQ i.
by rewrite !(@polynomial_coefficient_add A B embed variable coefficient hP) hDP hDQ mulrDr.
Qed.

(** Source for [formal_polynomial_derivative_opp]:
    negation in the cited formal differentiation laws. *)
Lemma formal_polynomial_derivative_opp (P DP:B):
  is_formal_polynomial_derivative coefficient P DP ->
  is_formal_polynomial_derivative coefficient (-P) (-DP).
Proof.
move=>hDP i.
by rewrite !(@polynomial_coefficient_opp A B embed variable coefficient hP) hDP mulrN.
Qed.

(** Source for [formal_polynomial_derivative_scalar]:
    multiplication by an original constant in the
    cited formal differentiation laws. *)
Lemma formal_polynomial_derivative_scalar (a:A) (P DP:B):
  is_formal_polynomial_derivative coefficient P DP ->
  is_formal_polynomial_derivative coefficient (embed a*P) (embed a*DP).
Proof.
move=>hDP i.
rewrite !(@polynomial_coefficient_scalar_multiply A B embed variable coefficient hP) hDP.
ring.
Qed.

(** Source for [formal_polynomial_derivative_variable]:
    the product rule for the original variable
    in the cited formal differentiation laws.
    Apply the existing coefficient-shift theorem. *)
Lemma formal_polynomial_derivative_variable (P DP:B):
  is_formal_polynomial_derivative coefficient P DP ->
  is_formal_polynomial_derivative coefficient (variable*P) (P+variable*DP).
Proof.
move=>hDP i.
rewrite (@polynomial_coefficient_add A B embed variable coefficient hP)
  !(@polynomial_variable_multiply_coefficient A B embed variable coefficient hP).
case:i=>[|i] /=.
- by rewrite ?addr0 ?mul1r.
- rewrite !subSS !subn0 hDP -[i.+2%:R]natr1;ring.
Qed.

(** Source for [formal_polynomial_derivative_linear_factor]:
    the product rule for an original linear root
    factor, used in the simple-root criterion of
    Bourbaki (1990), Chapter IV, section 2,
    no. 2, Proposition 7, p. IV.17. *)
Theorem formal_polynomial_derivative_linear_factor (a:A) (P DP:B):
  is_formal_polynomial_derivative coefficient P DP ->
  is_formal_polynomial_derivative coefficient ((variable-embed a)*P)
    (P+(variable-embed a)*DP).
Proof.
move=>hDP.
have hVariable:=formal_polynomial_derivative_variable hDP.
have hScalar:=formal_polynomial_derivative_scalar a hDP.
have hNegative:=formal_polynomial_derivative_opp hScalar.
have hSum:=formal_polynomial_derivative_add hVariable hNegative.
have hInput:variable*P+ -(embed a*P) = (variable-embed a)*P by ring.
have hOutput:(P+variable*DP)+ -(embed a*DP) = P+(variable-embed a)*DP by ring.
by rewrite hInput hOutput in hSum.
Qed.

(** Source for [formal_polynomial_derivative_at_linear_root]:
    at an original root, the derivative of
    (X-a)P equals the value of P, the cited
    Proposition 7, p. IV.17. Uniqueness connects
    the independently specified derivatives. *)
Theorem formal_polynomial_derivative_at_linear_root (C:comNzRingType)
  (E:{rmorphism B->C}) (a:A) (P DP D:B):
  is_formal_polynomial_derivative coefficient P DP ->
  is_formal_polynomial_derivative coefficient ((variable-embed a)*P) D ->
  E (variable-embed a) = 0 ->E D = E P.
Proof.
move=>hDP hD hRoot.
have hCandidate:=formal_polynomial_derivative_linear_factor a hDP.
have hEqual:=@formal_polynomial_derivative_unique A B embed variable coefficient hP
  ((variable-embed a)*P) D (P+(variable-embed a)*DP) hD hCandidate.
by rewrite hEqual rmorphD rmorphM hRoot mul0r addr0.
Qed.
End Laws.
