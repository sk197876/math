(** Federer (1969), 3.4.7, p. 325: polynomial
    primes remain prime when analytic division has the
    original unique finite remainders. This supporting algebraic
    argument uses independently stated division properties;
    their analytic instances are proved separately. *)
From mathcomp Require Import all_boot all_order ssralg boolp ring.
From Federer Require Import CommutativeDomainUP CommutativeFactorizationUP
  CommutativePolynomialUP CommutativePolynomialBasicLaws CommutativePolynomialMonicUP
  PolynomialMonicDivision PolynomialMonicPrimeBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [polynomial_prime_unique_division_lift]: the
    actual smaller-degree remainder comparison transfers a
    prime factor from the polynomial subring into the
    ambient ring, supporting the expanded analytic argument
    in 3.4.7, p. 325. Neither primality nor
    irreducibility of its ambient image is a premise. *)
Theorem polynomial_prime_unique_division_lift (A B C:comNzRingType)
    (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
    (hP:is_commutative_polynomial_ring embed variable coefficient)
    (hDomain:is_commutative_integral_domain A) (H:B) n (J:{rmorphism B->C}):
  injective J ->is_monic_polynomial coefficient H n ->is_commutative_prime_element H ->
  (forall x:C,exists a:C,exists r:B,
    (forall i,(n<=i)%N ->coefficient r i = 0) /\x = a*J H+J r) ->
  (forall (a:C) (r:B),(forall i,(n<=i)%N ->coefficient r i = 0) ->
    0 = a*J H+J r ->r = 0) ->
  is_commutative_prime_element (J H).
Proof.
move=>hInjective hMonic hPrime hDivision hUnique.
have hPositive:=@polynomial_monic_prime_positive_degree A B embed variable coefficient hP H n hMonic hPrime.
split.
- move=>hZero;apply:hPrime.1;apply:hInjective;by rewrite hZero rmorph0.
- split.
  + move=>[u hu].
    have hBound:forall i,(n<=i)%N ->coefficient (-1:B) i = 0.
      move=>i hi.
      rewrite (@polynomial_coefficient_opp A B embed variable coefficient hP)
        (@polynomial_coefficient_one A B embed variable coefficient hP).
      have hIPositive:(0<i)%N:=leq_trans hPositive hi.
      have hNe:(i==0%N) = false by apply/negP=>/eqP h;by rewrite h ltnn in hIPositive.
      by rewrite hNe oppr0.
    have hZero:0 = u*J H+J (-1) by rewrite hu rmorphN rmorph1 subrr.
    have hBad:=hUnique u (-1) hBound hZero.
    have hNonzero:(-1:B)!=0 by rewrite oppr_eq0 oner_eq0.
    by rewrite hBad eqxx in hNonzero.
  + move=>x y [c hProduct].
    have [a [r [hRBound hX]]]:=hDivision x.
    have [b [s [hSBound hY]]]:=hDivision y.
    have [q [t [hDivide hTBound]]]:=@polynomial_monic_division A B embed variable coefficient
      hP hDomain H n hMonic.1 hMonic.2 (r*s).
    have hBoundT:forall i,(n<=i)%N ->coefficient t i = 0.
      case:hTBound=>[hZero|[d [hSmaller hDegree]]].
      * move=>i _;rewrite hZero;exact:(@polynomial_coefficient_zero A B embed variable coefficient hP i).
      * move=>i hi;apply:hDegree.2;exact:leq_trans hSmaller hi.
    have hRS:J r*J s = J q*J H+J t.
      by rewrite -rmorphM hDivide rmorphD rmorphM.
    have hExpand:x*y = (a*b*J H+a*J s+b*J r+J q)*J H+J t.
      rewrite hX hY.
      transitivity ((a*b*J H+a*J s+b*J r)*J H+J r*J s);first ring.
      rewrite hRS;ring.
    have hZero:0 = (a*b*J H+a*J s+b*J r+J q-c)*J H+J t.
      have hDifference:=congr1 (fun z:C=>z-c*J H) hExpand.
      rewrite hProduct subrr in hDifference.
      rewrite hDifference;ring.
    have hTZero:=hUnique _ _ hBoundT hZero.
    have hDivides:commutative_divides H (r*s).
      exists q;by rewrite hDivide hTZero addr0.
    case:(hPrime.2.2 r s hDivides)=>h.
    * have hRZero:=@polynomial_bounded_divisible_zero A B embed variable coefficient hP
        hDomain H r n hMonic.1 hRBound h.
      left;exists a;by rewrite hX hRZero rmorph0 addr0.
    * have hSZero:=@polynomial_bounded_divisible_zero A B embed variable coefficient hP
        hDomain H s n hMonic.1 hSBound h.
      right;exists b;by rewrite hY hSZero rmorph0 addr0.
Qed.
