(** Federer (1969), 3.4.7, p. 325: normalize the
    polynomial factors of the original prepared polynomial.
    Their leading coefficients multiply to one, so the
    opposite leading coefficients give actual monic associates. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeDomainUP CommutativeFactorizationUP
  CommutativePolynomialUP CommutativePolynomialBasicLaws CommutativePolynomialDegreeUP
  CommutativePolynomialDegree CommutativePolynomialProductDegree PolynomialLeadingCoefficient
  CommutativePolynomialMonicUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [polynomial_monic_factor_normalization]: each
    actual factor of a monic prepared polynomial has a
    monic associate, with unchanged degree and exact product,
    supporting the factor comparison in 3.4.7, p. 325. *)
Theorem polynomial_monic_factor_normalization (A B:comNzRingType)
    (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
    (hP:is_commutative_polynomial_ring embed variable coefficient)
    (hDomain:is_commutative_integral_domain A) (P H Q:B) k m n:
  is_monic_polynomial coefficient P k ->
  is_polynomial_degree coefficient H m ->is_polynomial_degree coefficient Q n ->
  P = H*Q ->exists H' Q':B,exists u v:A,
    is_monic_polynomial coefficient H' m /\is_monic_polynomial coefficient Q' n /\
    H'*Q' = P /\is_commutative_unit u /\is_commutative_unit v /\
    H' = embed u*H /\Q' = embed v*Q.
Proof.
move=>[hDegreeP hMonicP] hDegreeH hDegreeQ hProduct.
have hDegreeProduct:=@polynomial_product_degree A B embed variable coefficient hP hDomain
  H Q m n hDegreeH hDegreeQ.
rewrite -hProduct in hDegreeProduct.
have hDegreeSum:=@polynomial_degree_unique A B coefficient P (m+n)%N k hDegreeProduct hDegreeP.
pose cH:=coefficient H m;pose cQ:=coefficient Q n.
have hLeading:cH*cQ = 1.
  have h:=@polynomial_product_leading_coefficient A B embed variable coefficient hP
    H Q m n hDegreeH.2 hDegreeQ.2.
  rewrite -hProduct hDegreeSum hMonicP in h;exact:esym h.
have hUnitH:is_commutative_unit cH by exists cQ;rewrite mulrC.
have hUnitQ:is_commutative_unit cQ by exists cH.
pose H':=embed cQ*H;pose Q':=embed cH*Q.
have hConstantQ:is_polynomial_degree coefficient (embed cQ) 0%N.
  have h:=@polynomial_monomial_degree A B embed variable coefficient hP cQ 0%N hDegreeQ.1.
  by rewrite expr0 mulr1 in h.
have hConstantH:is_polynomial_degree coefficient (embed cH) 0%N.
  have h:=@polynomial_monomial_degree A B embed variable coefficient hP cH 0%N hDegreeH.1.
  by rewrite expr0 mulr1 in h.
have hMonicH:is_monic_polynomial coefficient H' m.
  split.
  - exact:(@polynomial_product_degree A B embed variable coefficient hP hDomain
      (embed cQ) H 0%N m hConstantQ hDegreeH).
  - have h:=@polynomial_product_leading_coefficient A B embed variable coefficient hP
      (embed cQ) H 0%N m hConstantQ.2 hDegreeH.2.
    rewrite add0n (@polynomial_coefficient_constant A B embed variable coefficient hP) /= in h.
    rewrite /H' h;by rewrite mulrC.
have hMonicQ:is_monic_polynomial coefficient Q' n.
  split.
  - exact:(@polynomial_product_degree A B embed variable coefficient hP hDomain
      (embed cH) Q 0%N n hConstantH hDegreeQ).
  - have h:=@polynomial_product_leading_coefficient A B embed variable coefficient hP
      (embed cH) Q 0%N n hConstantH.2 hDegreeQ.2.
    rewrite add0n (@polynomial_coefficient_constant A B embed variable coefficient hP) /= in h.
    by rewrite /Q' h.
have hRestore:H'*Q' = P.
  rewrite /H' /Q' mulrACA -rmorphM [cQ*cH]mulrC hLeading rmorph1 mul1r.
  exact:esym hProduct.
exists H',Q',cQ,cH.
split;first exact:hMonicH.
split;first exact:hMonicQ.
split;first exact:hRestore.
split;first exact:hUnitQ.
split;first exact:hUnitH.
by split.
Qed.
