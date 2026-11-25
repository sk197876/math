(** Federer (1969), 3.4.8(10), p. 331:
    the original prefix induction first treats
    the prepared polynomial and then its
    bounded division remainder. Apply the
    checked bounded-polynomial prefix step twice
    and the original ideal laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativeQuotientUP CommutativeSubringUP
  CommutativeIdealSaturationUP CommutativeIdealSaturationLaws CommutativePolynomialUP
  CommutativePolynomialEvaluationUP PolynomialSaturationPrefixStep.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [polynomial_saturation_division_step]:
    the original previous-prefix assertion and
    analytic division imply the next-prefix
    assertion, 3.4.8(10), p. 331.
    The prepared polynomial and every bounded
    remainder use the same original coordinate
    equation modulo the saturation. No
    next-prefix ideal conclusion is assumed. *)
Theorem polynomial_saturation_division_step (A B C D:comNzRingType)
  (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
  (hP:is_commutative_polynomial_ring embed variable coefficient)
  (phi:{rmorphism A->C}) (t:C) (J:{rmorphism B->C})
  (F I S Q next:set C) (delta z:C) (pi:{rmorphism C->D}) (H:B) k:
  is_commutative_ideal F ->is_commutative_ideal I ->
  is_commutative_ideal_saturation F delta S ->is_commutative_ideal_quotient S pi ->
  S `<=` I ->is_commutative_subring Q ->(forall a:A,Q (phi a)) ->Q delta ->Q z ->
  (forall x:C,I x ->Q x ->S x) ->S (delta*t-z) ->
  is_commutative_polynomial_evaluation embed variable phi t J ->I (J H) ->
  (forall alpha:C,next alpha ->exists a:C,exists r:B,
    (forall i,(k<=i)%N ->coefficient r i = 0) /\alpha = a*J H+J r) ->
  forall alpha:C,I alpha ->next alpha ->S alpha.
Proof.
move=>hF hI hS hPi hSI hQ hCoefficients hDelta hZ hPrevious hRelation hJ hPrepared hDivision.
have hSIdeal:=@commutative_ideal_saturation_is_ideal C F delta S hF hS.
have [N hSupportH]:=@polynomial_coefficients_finite A B embed variable coefficient hP H.
have hPreparedS:=@polynomial_saturation_prefix_step A B C D embed variable coefficient hP
  phi t J F I S Q delta z pi H N hF hI hS hPi hSI hQ hCoefficients hDelta hZ
  hPrevious hRelation hJ hSupportH hPrepared.
move=>alpha hAlpha hNext.
have [a [r [hSupport hEquation]]]:=hDivision alpha hNext.
have hProductI:I (a*J H):=@commutative_ideal_mul C I hI a (J H) hPrepared.
have hRemainderI:I (J r).
  have hDifference:=@commutative_ideal_add C I hI alpha (-(a*J H)) hAlpha
    (@commutative_ideal_opp C I hI _ hProductI).
  by rewrite hEquation addrAC subrr add0r in hDifference.
have hRemainderS:=@polynomial_saturation_prefix_step A B C D embed variable coefficient hP
  phi t J F I S Q delta z pi r k hF hI hS hPi hSI hQ hCoefficients hDelta hZ
  hPrevious hRelation hJ hSupport hRemainderI.
have hProductS:=@commutative_ideal_mul C S hSIdeal a (J H) hPreparedS.
rewrite hEquation;exact:(@commutative_ideal_add C S hSIdeal _ _ hProductS hRemainderS).
Qed.
