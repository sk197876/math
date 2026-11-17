(** Federer (1969), 3.4.7, p. 325: a common
    nonzero coefficient divisor factors from the actual polynomial.
    The quotient coefficients and their finite support are proved. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeDomainUP CommutativeDomainCancellation CommutativeFactorizationUP
  CommutativePolynomialUP CommutativePolynomialBasicLaws CommutativePolynomialFiniteSums
  NaturalConvolution NaturalConvolutionMonomial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [polynomial_coefficient_scalar_multiply]: multiplying
    by an original constant multiplies every coefficient,
    supporting the content argument in 3.4.7, p. 325. *)
Lemma polynomial_coefficient_scalar_multiply (A B:comNzRingType)
    (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
    (hP:is_commutative_polynomial_ring embed variable coefficient) (a:A) (P:B) n:
  coefficient (embed a*P) n = a*coefficient P n.
Proof.
rewrite (@polynomial_coefficient_multiply A B embed variable coefficient hP).
transitivity (natural_coefficient_convolution (fun i=>if i==0%N then a else 0) (coefficient P) n).
  rewrite /natural_coefficient_convolution big_mkord;apply:eq_bigr=>i _.
  by rewrite (@polynomial_coefficient_constant A B embed variable coefficient hP).
by rewrite natural_convolution_monomial leq0n subn0.
Qed.

(** Source for [polynomial_coefficient_division]: any common
    nonzero coefficient divisor factors from the actual polynomial,
    supporting Gauss's lemma in 3.4.7, p. 325.
    No polynomial quotient is supplied as a premise. *)
Theorem polynomial_coefficient_division (A B:comNzRingType)
    (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
    (hP:is_commutative_polynomial_ring embed variable coefficient)
    (hDomain:is_commutative_integral_domain A) (a:A) (P:B):
  a<>0 ->(forall i,commutative_divides a (coefficient P i)) ->
  exists Q:B,P = embed a*Q.
Proof.
move=>ha hDivides.
have hChoices:forall i,exists c,coefficient P i = a*c.
  move=>i;have [c hc]:=hDivides i;exists c;by rewrite mulrC.
pose f i:=projT1 (cid (hChoices i)).
have hF i:coefficient P i = a*f i:=projT2 (cid (hChoices i)).
have [N hN]:=@polynomial_coefficients_finite A B embed variable coefficient hP P.
have hFinite:exists N,forall i,(N<=i)%N ->f i = 0.
  exists N=>i hi.
  apply:(@commutative_domain_cancel_left A hDomain a (f i) 0 ha).
  by rewrite -hF hN // mulr0.
have [Q hQ]:=@polynomial_interpolation_exists A B embed variable coefficient hP f hFinite.
exists Q;apply:(@polynomial_coefficients_unique A B embed variable coefficient hP)=>i.
by rewrite (@polynomial_coefficient_scalar_multiply A B embed variable coefficient hP) hQ -hF.
Qed.
