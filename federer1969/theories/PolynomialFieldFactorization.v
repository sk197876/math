(** Federer (1969), 3.4.7, p. 325: prime
    factorization over the coefficient fraction field, supporting
    the Gauss argument. Actual division, principal ideals,
    Bezout combinations and degree induction prove this theorem. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets ring.
From Federer Require Import CommutativeDomainUP CommutativeFactorizationUP CommutativeUnitLaws
  CommutativePolynomialUP CommutativePolynomialDegreeUP CommutativePolynomialDegree
  CommutativePolynomialProductDegree PolynomialFieldUnits PolynomialFieldPrincipalIdeals
  PrincipalIdealIrreduciblePrime.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [polynomial_field_prime_factorization]: the
    field polynomial ring is a unique-factorization domain
    in the prime-factorization specification used by the
    Gauss lemma in 3.4.7, p. 325. No
    polynomial factorization theorem is imported. *)
Theorem polynomial_field_prime_factorization (K:fieldType) (B:comNzRingType)
    (embed:{rmorphism K->B}) (variable:B) (coefficient:B->nat->K)
    (hP:is_commutative_polynomial_ring embed variable coefficient):
  is_unique_factorization_commutative_domain B.
Proof.
have hFieldDomain:is_commutative_integral_domain K.
  move=>x y h;case:(eqVneq x 0)=>[hx|hx];first by left.
  right;apply:(mulfI hx);by rewrite h mulr0.
have hDomain:=@polynomial_ring_domain K B embed variable coefficient hP hFieldDomain.
have hPrincipal:=@polynomial_field_principal_ideals K B embed variable coefficient hP.
have hPrime:=@principal_ideal_irreducible_prime B hPrincipal.
have hPositive (P:B) n:is_polynomial_degree coefficient P n ->
    ~is_commutative_unit P ->(0<n)%N.
  move=>hDegree hNonunit;rewrite lt0n;apply/eqP=>hZero.
  apply:hNonunit;apply:(@polynomial_degree_zero_unit K B embed variable coefficient hP).
  by rewrite -hZero.
have hMain:forall n (P:B),is_polynomial_degree coefficient P n ->
    exists u:B,exists F:seq B,is_commutative_unit u /\
      (forall p,p\in F ->is_commutative_prime_element p) /\P = u*\prod_(p<-F) p.
  move=>n;elim/ltn_ind:n=>n ih P hDegree.
  case:(pselect (is_commutative_unit P))=>[hUnit|hNonunit].
  - exists P,[::];split;first exact:hUnit.
    split;first by move=>p;rewrite in_nil.
    by rewrite big_nil mulr1.
  - case:(pselect (is_commutative_irreducible P))=>[hIrreducible|hReducible].
    + exists 1,[::P];split;first exact:commutative_one_unit.
      split.
      * move=>p;rewrite in_cons in_nil orbF=>/eqP->;exact:hPrime P hIrreducible.
      * by rewrite big_cons big_nil mulr1 mul1r.
    + have hNonzero:P<>0.
        move=>hZero;apply:hDegree.1;rewrite hZero.
        exact:(@polynomial_coefficient_zero K B embed variable coefficient hP n).
      have hFactors:exists U V:B,P = U*V /\~is_commutative_unit U /\~is_commutative_unit V.
        apply:contrapT=>hNoFactors;apply:hReducible;split;first exact:hNonzero.
        split;first exact:hNonunit.
        move=>U V hProduct;case:(pselect (is_commutative_unit U))=>[h|h];first by left.
        right;apply:contrapT=>hV;apply:hNoFactors;by exists U,V.
      have [U [V [hProduct [hUNonunit hVNonunit]]]]:=hFactors.
      have hUNonzero:U<>0 by move=>h;apply:hNonzero;by rewrite hProduct h mul0r.
      have hVNonzero:V<>0 by move=>h;apply:hNonzero;by rewrite hProduct h mulr0.
      have [m hDegreeU]:=@polynomial_degree_exists K B embed variable coefficient hP U hUNonzero.
      have [k hDegreeV]:=@polynomial_degree_exists K B embed variable coefficient hP V hVNonzero.
      have hMPositive:=hPositive U m hDegreeU hUNonunit.
      have hKPositive:=hPositive V k hDegreeV hVNonunit.
      have hProductDegree:=@polynomial_product_degree K B embed variable coefficient hP hFieldDomain
        U V m k hDegreeU hDegreeV.
      rewrite -hProduct in hProductDegree.
      have hSum:=@polynomial_degree_unique K B coefficient P (m+k)%N n hProductDegree hDegree.
      have hMSmaller:(m<n)%N by rewrite -hSum -{1}(addn0 m) ltn_add2l.
      have hKSmaller:(k<n)%N by rewrite -hSum -{1}(add0n k) ltn_add2r.
      have [u [F [hu [hF hU]]]]:=ih m hMSmaller U hDegreeU.
      have [v [G [hv [hG hV]]]]:=ih k hKSmaller V hDegreeV.
      exists (u*v),(F++G);split.
      * apply/commutative_product_unit;by split.
      * split.
        -- move=>p;rewrite mem_cat=>/orP[h|h];[exact:hF p h|exact:hG p h].
        -- rewrite hProduct hU hV big_cat;exact:mulrACA.
split;first exact:hDomain.
move=>P hNonzero;have [n hDegree]:=@polynomial_degree_exists K B embed variable coefficient hP P hNonzero.
exact:hMain n P hDegree.
Qed.
