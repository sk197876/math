(** Federer (1969), 3.4.7, p. 325: factors
    of the original distinguished power have no lower
    coefficients. Degree and first nonzero order add,
    and equality of their sums forces equality for
    each factor. No factorization conclusion is assumed. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeDomainUP CommutativePolynomialUP
  CommutativePolynomialDegreeUP CommutativePolynomialDegree CommutativePolynomialProductDegree
  CommutativePolynomialOrderUP CommutativePolynomialOrder PolynomialLeadingCoefficient NaturalSumSaturation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [polynomial_factors_of_variable_power]: every
    original factor of a variable power has all
    coefficients below its degree zero, supporting the
    specialization of Weierstrass factors in 3.4.7, p. 325. *)
Theorem polynomial_factors_of_variable_power (A B:comNzRingType)
    (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
    (hP:is_commutative_polynomial_ring embed variable coefficient)
    (hDomain:is_commutative_integral_domain A) (P Q:B) m n k:
  is_polynomial_degree coefficient P m ->is_polynomial_degree coefficient Q n ->
  P*Q = variable^+k ->
  (forall i,(i<m)%N ->coefficient P i = 0) /\
  (forall i,(i<n)%N ->coefficient Q i = 0).
Proof.
move=>hDegreeP hDegreeQ hProduct.
have hPNonzero:P<>0.
  move=>hZero;apply:hDegreeP.1;rewrite hZero.
  exact:(@polynomial_coefficient_zero A B embed variable coefficient hP m).
have hQNonzero:Q<>0.
  move=>hZero;apply:hDegreeQ.1;rewrite hZero.
  exact:(@polynomial_coefficient_zero A B embed variable coefficient hP n).
have [u hOrderP]:=@polynomial_order_exists A B embed variable coefficient hP P hPNonzero.
have [v hOrderQ]:=@polynomial_order_exists A B embed variable coefficient hP Q hQNonzero.
have hProductOrder:=@polynomial_product_order A B embed variable coefficient hP hDomain
  P Q u v hOrderP hOrderQ.
rewrite hProduct in hProductOrder.
have hPowerOrder:=@polynomial_variable_power_order A B embed variable coefficient hP k.
have hOrderSum:=@polynomial_order_unique A B coefficient (variable^+k) (u+v)%N k
  hProductOrder hPowerOrder.
have hOne:(1:A)<>0 by apply/eqP;exact:oner_neq0.
have hPowerDegree:=@polynomial_monomial_degree A B embed variable coefficient hP 1 k hOne.
rewrite rmorph1 mul1r in hPowerDegree.
have hProductDegree:=@polynomial_product_degree A B embed variable coefficient hP hDomain
  P Q m n hDegreeP hDegreeQ.
rewrite hProduct in hProductDegree.
have hDegreeSum:=@polynomial_degree_unique A B coefficient (variable^+k) (m+n)%N k
  hProductDegree hPowerDegree.
have hU:=@polynomial_order_at_most_degree A B coefficient P u m hOrderP hDegreeP.
have hV:=@polynomial_order_at_most_degree A B coefficient Q v n hOrderQ hDegreeQ.
have hSum:(u+v = m+n)%N by rewrite hOrderSum hDegreeSum.
have [hUM hVN]:=natural_equal_sum_bounds_saturated hU hV hSum.
split.
- move=>i hi;apply:hOrderP.2;by rewrite hUM.
- move=>i hi;apply:hOrderQ.2;by rewrite hVN.
Qed.
