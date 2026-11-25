(** Federer (1969), 3.4.8(10), p. 330:
    formal differentiation has the printed
    finite polynomial evaluation. Connect the
    existing derivative coefficient equation and
    finite polynomial-evaluation theorem by shifting
    one finite index. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialEvaluationUP
  CommutativePolynomialEvaluationLaws FormalPolynomialDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [formal_derivative_evaluation_finite_expression]:
    the original W'_(m+1) is the
    finite sum of i times its
    original coefficient times the (i-1)st
    coordinate power, 3.4.8(10), p. 330.
    The zero-index term is zero; no
    positive-degree or characteristic hypothesis is needed. *)
Theorem formal_derivative_evaluation_finite_expression (A B C:comNzRingType)
  (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
  (hP:is_commutative_polynomial_ring embed variable coefficient)
  (phi:{rmorphism A->C}) (t:C) (J:{rmorphism B->C}) (W derivative:B) N:
  is_commutative_polynomial_evaluation embed variable phi t J ->
  is_formal_polynomial_derivative coefficient W derivative ->
  (forall i,(N<=i)%N ->coefficient W i = 0) ->
  J derivative = \sum_(i<N) (i:nat)%:R*phi (coefficient W i)*t^+(i:nat).-1.
Proof.
move=>hJ hDerivative hSupport.
have hBound i (hI:(N<=i)%N):coefficient derivative i = 0.
  by rewrite hDerivative hSupport //;[exact:mulr0|exact:leq_trans hI (leqnSn i)].
rewrite (@polynomial_evaluation_finite_expression A B C embed variable coefficient hP
  phi t J hJ derivative N hBound).
under eq_bigr do rewrite hDerivative rmorphM rmorph_nat.
clear hBound.
case:N hSupport=>[|N] hSupport;first by rewrite !big_ord0.
rewrite [LHS]big_ord_recr [RHS]big_ord_recl /= (hSupport N.+1 (leqnn N.+1)) rmorph0 mulr0 mul0r addr0.
by rewrite mul0r mul0r add0r.
Qed.
