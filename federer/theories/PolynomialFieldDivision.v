(** Federer (1969), 3.4.7, p. 325: actual field
    polynomial division supporting the Gauss argument. Leading-term
    cancellation and degree induction supply the quotient and
    remainder; no external division theorem is imported. *)
From mathcomp Require Import all_boot all_order ssralg boolp ring.
From Federer Require Import CommutativeDomainUP CommutativePolynomialUP
  CommutativePolynomialBasicLaws CommutativePolynomialDegreeUP CommutativePolynomialDegree
  CommutativePolynomialDegreeBounds CommutativePolynomialProductDegree PolynomialLeadingCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [polynomial_field_division]: division by
    an actual nonzero polynomial over a field has
    an actual remainder of smaller degree, supporting
    the Gauss lemma in 3.4.7, p. 325. *)
Theorem polynomial_field_division (K:fieldType) (B:comNzRingType)
    (embed:{rmorphism K->B}) (variable:B) (coefficient:B->nat->K)
    (hP:is_commutative_polynomial_ring embed variable coefficient) (Q:B) n:
  is_polynomial_degree coefficient Q n ->forall P:B,
  exists q r:B,P = q*Q+r /\
    (r = 0 \/exists d,(d<n)%N /\is_polynomial_degree coefficient r d).
Proof.
move=>hDegreeQ.
have hFieldDomain:is_commutative_integral_domain K.
  move=>x y h;case:(eqVneq x 0)=>[hx|hx];first by left.
  right;apply:(mulfI hx);by rewrite h mulr0.
have hQLeading:coefficient Q n!=0 by apply/eqP;exact:hDegreeQ.1.
have hMain:forall m (P:B),is_polynomial_degree coefficient P m ->
    exists q r:B,P = q*Q+r /\
      (r = 0 \/exists d,(d<n)%N /\is_polynomial_degree coefficient r d).
  move=>m;elim/ltn_ind:m=>m ih P hDegreeP.
  case:(ltnP m n)=>hMN.
  - exists 0,P;split;first by rewrite mul0r add0r.
    right;by exists m.
  - pose c:=coefficient P m/coefficient Q n.
    have hc:c<>0.
      move=>hZero;apply:hDegreeP.1.
      have h:=congr1 (fun a:K=>a*coefficient Q n) hZero.
      by rewrite /c divfK // mul0r in h.
    pose T:=embed c*variable^+(m-n)%N.
    have hDegreeT:is_polynomial_degree coefficient T (m-n)%N.
      exact:(@polynomial_monomial_degree K B embed variable coefficient hP c (m-n)%N hc).
    have hDegreeTQ:=@polynomial_product_degree K B embed variable coefficient hP hFieldDomain
      T Q (m-n)%N n hDegreeT hDegreeQ.
    rewrite (subnK hMN) in hDegreeTQ.
    have hTCoefficient:coefficient T (m-n)%N = c.
      by rewrite /T (@polynomial_monomial_coefficient K B embed variable coefficient hP) eqxx.
    have hTQCoefficient:coefficient (T*Q) m = coefficient P m.
      have h:=@polynomial_product_leading_coefficient K B embed variable coefficient hP
        T Q (m-n)%N n hDegreeT.2 hDegreeQ.2.
      by rewrite (subnK hMN) hTCoefficient /c divfK // in h.
    pose S:=P-T*Q.
    have hSBound:forall i,(m<=i)%N ->coefficient S i = 0.
      exact:(@polynomial_cancelled_leading_bound K B embed variable coefficient hP
        P (T*Q) m hDegreeP.2 hDegreeTQ.2 (esym hTQCoefficient)).
    case:(eqVneq S 0)=>[hSZero|hSNonzero].
    + have hProduct:P = T*Q:=subr0_eq hSZero.
      exists T,0;split;first by rewrite hProduct addr0.
      by left.
    + have hSNotZero:S<>0 by apply/eqP;exact:hSNonzero.
      have [d hDegreeS]:=@polynomial_degree_exists K B embed variable coefficient hP S hSNotZero.
      have hSmaller:=@polynomial_degree_below_support_bound K B coefficient
        S d m hDegreeS hSBound.
      have [q [r [hDivision hRemainder]]]:=ih d hSmaller S hDegreeS.
      exists (q+T),r;split;last exact:hRemainder.
      have hRestore:P = S+T*Q by rewrite /S subrK.
      rewrite {1}hRestore hDivision;ring.
move=>P;case:(eqVneq P 0)=>[hZero|hNonzero].
- exists 0,0;split;first by rewrite hZero mul0r add0r.
  by left.
- have hPNotZero:P<>0 by apply/eqP;exact:hNonzero.
  have [m hDegreeP]:=@polynomial_degree_exists K B embed variable coefficient hP P hPNotZero.
  exact:hMain m P hDegreeP.
Qed.
