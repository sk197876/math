(** Federer (1969), 3.4.7, p. 325: a
    monic prime has positive degree, and divisibility
    cannot leave a nonzero smaller-degree remainder.
    These supporting consequences use the original polynomial
    laws and domain property. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeDomainUP CommutativeFactorizationUP CommutativeUnitLaws
  CommutativePolynomialUP CommutativePolynomialDegreeUP CommutativePolynomialDegree
  CommutativePolynomialDegreeBounds CommutativePolynomialProductDegree CommutativePolynomialMonicUP
  CommutativePolynomialBasicLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Bounds.
Variables A B:comNzRingType.
Variable embed:{rmorphism A->B}.
Variable variable:B.
Variable coefficient:B->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.

(** Source for [polynomial_monic_degree_zero_one]: the
    degree-zero monic factor is one, supporting the
    prime normalization in 3.4.7, p. 325. *)
Lemma polynomial_monic_degree_zero_one (P:B):
  is_monic_polynomial coefficient P 0%N ->P = 1.
Proof.
move=>[hDegree hLeading].
by rewrite (@polynomial_degree_zero_constant A B embed variable coefficient hP P hDegree)
  hLeading rmorph1.
Qed.

(** Source for [polynomial_monic_prime_positive_degree]: a
    normalized original prime factor cannot have degree
    zero, supporting degree descent in 3.4.7, p. 325. *)
Lemma polynomial_monic_prime_positive_degree (P:B) n:
  is_monic_polynomial coefficient P n ->is_commutative_prime_element P ->(0<n)%N.
Proof.
case:n=>[|n] hMonic hPrime;last by [].
exfalso;apply:hPrime.2.1.
rewrite (polynomial_monic_degree_zero_one hMonic).
exact:commutative_one_unit.
Qed.

(** Source for [polynomial_bounded_divisible_zero]: a
    remainder supported below the divisor degree and
    divisible by that divisor is zero, supporting
    the analytic prime comparison in 3.4.7, p. 325. *)
Theorem polynomial_bounded_divisible_zero
    (hDomain:is_commutative_integral_domain A) (H P:B) n:
  is_polynomial_degree coefficient H n ->
  (forall i,(n<=i)%N ->coefficient P i = 0) ->
  commutative_divides H P ->P = 0.
Proof.
move=>hDegreeH hSupport [Q hProduct].
case:(eqVneq P 0)=>[hZero|hNonzero];first exact:hZero.
exfalso.
have hPNonzero:P<>0 by apply/eqP;exact:hNonzero.
have hQNonzero:Q<>0 by move=>hZero;apply:hPNonzero;by rewrite hProduct hZero mul0r.
have [d hDegreeP]:=@polynomial_degree_exists A B embed variable coefficient hP P hPNonzero.
have hSmaller:=@polynomial_degree_below_support_bound A B coefficient P d n hDegreeP hSupport.
have [m hDegreeQ]:=@polynomial_degree_exists A B embed variable coefficient hP Q hQNonzero.
have hDegreeProduct:=@polynomial_product_degree A B embed variable coefficient hP hDomain
  Q H m n hDegreeQ hDegreeH.
rewrite -hProduct in hDegreeProduct.
have hEqual:=@polynomial_degree_unique A B coefficient P d (m+n)%N hDegreeP hDegreeProduct.
rewrite hEqual in hSmaller.
have hBound:(n<=m+n)%N by rewrite leq_addl.
by rewrite (leq_gtF hBound) in hSmaller.
Qed.

(** Source for [polynomial_positive_degree_not_unit]: an
    original positive-degree polynomial cannot be invertible
    over a domain, supporting the prime-factor selection
    in 3.4.7, p. 325. *)
Lemma polynomial_positive_degree_not_unit
    (hDomain:is_commutative_integral_domain A) (P:B) n:
  is_polynomial_degree coefficient P n ->(0<n)%N ->~is_commutative_unit P.
Proof.
move=>hDegreeP hPositive [Q hProduct].
have hQNonzero:Q<>0.
  move=>hZero;rewrite hZero mul0r in hProduct.
  have hOne:(1:B)!=0:=oner_neq0 B.
  by rewrite -hProduct eqxx in hOne.
have [m hDegreeQ]:=@polynomial_degree_exists A B embed variable coefficient hP Q hQNonzero.
have hDegreeProduct:=@polynomial_product_degree A B embed variable coefficient hP hDomain
  Q P m n hDegreeQ hDegreeP.
rewrite hProduct in hDegreeProduct.
have hDegreeOne:is_polynomial_degree coefficient (1:B) 0%N.
  split.
  - rewrite (@polynomial_coefficient_one A B embed variable coefficient hP) /=.
    move=>hZero;have hOne:(1:A)!=0:=oner_neq0 A;by rewrite hZero eqxx in hOne.
  - move=>i hi;rewrite (@polynomial_coefficient_one A B embed variable coefficient hP).
    have hNe:(i==0%N) = false by apply/negP=>/eqP h;by rewrite h ltnn in hi.
    by rewrite hNe.
have hEqual:=@polynomial_degree_unique A B coefficient (1:B) (m+n)%N 0%N hDegreeProduct hDegreeOne.
have hSumPositive:(0<m+n)%N:=leq_trans hPositive (leq_addl m n).
by rewrite hEqual ltnn in hSumPositive.
Qed.
End Bounds.
