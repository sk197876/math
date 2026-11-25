(** Federer (1969), 3.4.7, p. 325: units of
    the field polynomial ring are exactly its nonzero
    constants. Actual coefficient degrees prove the assertion. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeDomainUP CommutativeFactorizationUP CommutativeUnitLaws
  CommutativePolynomialUP CommutativePolynomialBasicLaws CommutativePolynomialDegreeUP
  CommutativePolynomialDegree CommutativePolynomialDegreeBounds CommutativePolynomialProductDegree.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Units.
Variable K:fieldType.
Variable B:comNzRingType.
Variable embed:{rmorphism K->B}.
Variable variable:B.
Variable coefficient:B->nat->K.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.

(** Source for [polynomial_one_degree]: the unit has
    degree zero, supporting the polynomial factorization
    argument in 3.4.7, p. 325. *)
Lemma polynomial_one_degree:is_polynomial_degree coefficient (1:B) 0%N.
Proof.
split.
- rewrite (@polynomial_coefficient_one K B embed variable coefficient hP) /=.
  by apply/eqP;exact:oner_neq0.
- move=>i hi;rewrite (@polynomial_coefficient_one K B embed variable coefficient hP).
  have hI:(i==0%N) = false by apply/negP=>/eqP h;by rewrite h ltnn in hi.
  by rewrite hI.
Qed.

(** Source for [polynomial_degree_zero_unit]: a degree-zero
    polynomial is an original nonzero scalar and is
    a unit, supporting 3.4.7, p. 325. *)
Lemma polynomial_degree_zero_unit (P:B):
  is_polynomial_degree coefficient P 0%N ->is_commutative_unit P.
Proof.
move=>hDegree;have hLeading:coefficient P 0%N!=0 by apply/eqP;exact:hDegree.1.
have hConstant:=@polynomial_degree_zero_constant K B embed variable coefficient hP P hDegree.
exists (embed (coefficient P 0%N)^-1).
by rewrite {2}hConstant -rmorphM (mulVf hLeading) rmorph1.
Qed.

(** Source for [polynomial_unit_degree_zero]: a unit
    cannot have positive degree, supporting the prime
    factorization argument in 3.4.7, p. 325. *)
Lemma polynomial_unit_degree_zero (P:B) n:
  is_polynomial_degree coefficient P n ->is_commutative_unit P ->n = 0%N.
Proof.
move=>hDegree [Q hInverse].
have hQNonzero:Q<>0.
  move=>hZero;move:hInverse;rewrite hZero mul0r=>h.
  by move:(oner_neq0 B);rewrite -h eqxx.
have [m hDegreeQ]:=@polynomial_degree_exists K B embed variable coefficient hP Q hQNonzero.
have hFieldDomain:is_commutative_integral_domain K.
  move=>x y h;case:(eqVneq x 0)=>[hx|hx];first by left.
  right;apply:(mulfI hx);by rewrite h mulr0.
have hProductDegree:=@polynomial_product_degree K B embed variable coefficient hP hFieldDomain
  Q P m n hDegreeQ hDegree.
rewrite hInverse in hProductDegree.
have hSumZero:=@polynomial_degree_unique K B coefficient 1 (m+n)%N 0%N
  hProductDegree polynomial_one_degree.
move/eqP:hSumZero;rewrite addn_eq0;move/andP=>[_ /eqP hN];exact:hN.
Qed.
End Units.
