(** Federer (1969), 3.4.7, p. 325: the
    original monic Weierstrass factors remain distinguished.
    Specializing the transverse coefficients gives a variable
    power. Additive order and degree prove the required
    vanishing for both factors. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeDomainUP CommutativePolynomialUP
  CommutativePolynomialBasicLaws CommutativePolynomialMonicUP PolynomialCoefficientMapUP
  PolynomialMonicCoefficientMap PolynomialFactorsOfPower DistinguishedPolynomialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Specialization.
Variables A B C D:comNzRingType.
Variable embed:{rmorphism A->B}.
Variable variable:B.
Variable coefficient:B->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable embedC:{rmorphism C->D}.
Variable variableC:D.
Variable target:D->nat->C.
Hypothesis hTarget:is_commutative_polynomial_ring embedC variableC target.
Variable value:{rmorphism A->C}.
Variable M:{rmorphism B->D}.
Hypothesis hMap:is_polynomial_coefficient_map coefficient target value M.

(** Source for [distinguished_polynomial_specialization_power]:
    the actual prepared polynomial restricts at the transverse
    origin to the original variable power, supporting
    3.4.7, p. 325. *)
Theorem distinguished_polynomial_specialization_power (P:B) k:
  is_distinguished_polynomial coefficient value P k ->M P = variableC^+k.
Proof.
move=>[[hDegree hLeading] hLower].
apply:(@polynomial_coefficients_unique C D embedC variableC target hTarget)=>i.
rewrite hMap (@polynomial_power_coefficient C D embedC variableC target hTarget).
case:(ltngtP i k)=>[hSmall|hLarge|hEqual].
- by rewrite hLower.
- by rewrite hDegree.2 // rmorph0.
- subst i;by rewrite hLeading rmorph1.
Qed.

(** Source for [distinguished_polynomial_monic_factors]: both
    normalized factors have all lower coefficients zero at
    the original transverse origin, supporting the genuine
    Weierstrass factors in 3.4.7, p. 325. No
    injectivity of the value map is assumed. *)
Theorem distinguished_polynomial_monic_factors
    (hDomain:is_commutative_integral_domain C) (P H Q:B) k m n:
  is_distinguished_polynomial coefficient value P k ->
  is_monic_polynomial coefficient H m ->is_monic_polynomial coefficient Q n ->
  P = H*Q ->
  is_distinguished_polynomial coefficient value H m /\
  is_distinguished_polynomial coefficient value Q n.
Proof.
move=>hDistinguished hH hQ hProduct.
have hMappedH:=@polynomial_coefficient_map_monic_degree A C B D coefficient target value M H m hMap hH.
have hMappedQ:=@polynomial_coefficient_map_monic_degree A C B D coefficient target value M Q n hMap hQ.
have hPower:M H*M Q = variableC^+k.
  rewrite -rmorphM -hProduct;exact:distinguished_polynomial_specialization_power hDistinguished.
have [hLowerH hLowerQ]:=@polynomial_factors_of_variable_power C D embedC variableC target
  hTarget hDomain (M H) (M Q) m n k hMappedH.1 hMappedQ.1 hPower.
split.
- split;first exact:hH.
  move=>i hi;rewrite -(hMap H i);exact:hLowerH i hi.
- split;first exact:hQ.
  move=>i hi;rewrite -(hMap Q i);exact:hLowerQ i hi.
Qed.
End Specialization.
