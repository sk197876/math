(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: an actual polynomial root gives
    its linear factor. Apply the existing field
    division and degree theorems from 3.4.7.
    Source: Bourbaki, Algebra II (1990), Chapter IV,
    section 2, no. 1, Proposition 1, pp. IV.14–15. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialBasicLaws
  CommutativeDomainUP CommutativePolynomialDegreeUP CommutativePolynomialDegree
  CommutativePolynomialDegreeBounds CommutativePolynomialProductDegree PolynomialFieldDivision.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Factor.
Variable K:fieldType.
Variable B:comNzRingType.
Variable embed:{rmorphism K->B}.
Variable variable:B.
Variable coefficient:B->nat->K.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.

(** Source for [polynomial_linear_root_factor_degree]:
    X-a has degree one; supporting the root-factor
    theorem in Bourbaki (1990), Chapter IV,
    section 2, no. 1, Proposition 1,
    pp. IV.14–15, used for 3.4.8(8), pp. 329–330. *)
Lemma polynomial_linear_root_factor_degree (a:K):
  is_polynomial_degree coefficient (variable-embed a) 1%N.
Proof.
split.
- rewrite (@polynomial_subtract_coefficients K B embed variable coefficient hP)
    (@polynomial_coefficient_variable K B embed variable coefficient hP)
    (@polynomial_coefficient_constant K B embed variable coefficient hP) /= subr0.
  by apply/eqP;exact:oner_neq0.
- move=>i hi.
  have hI1:(i==1%N) = false.
    apply/negP=>/eqP h;by rewrite h ltnn in hi.
  have hI0:(i==0%N) = false.
    apply/negP=>/eqP h;by rewrite h ltn0 in hi.
  by rewrite (@polynomial_subtract_coefficients K B embed variable coefficient hP)
    (@polynomial_coefficient_variable K B embed variable coefficient hP)
    (@polynomial_coefficient_constant K B embed variable coefficient hP) hI1 hI0 subrr.
Qed.

(** Source for [polynomial_linear_factor_from_root]:
    an original root a gives divisibility by X-a;
    Bourbaki (1990), Chapter IV, section 2,
    no. 1, Proposition 1, pp. IV.14–15.
    This supports the finite-separable argument of
    3.4.8(8), pp. 329–330. Reuse field division
    and the already proved constant-remainder law. *)
Theorem polynomial_linear_factor_from_root (a:K) (E:{rmorphism B->K}):
  (forall c:K,E (embed c) = c) ->E variable = a ->forall P:B,E P = 0 ->
    exists Q:B,P = Q*(variable-embed a).
Proof.
move=>hConstants hVariable P hRoot.
have hLinearZero:E (variable-embed a) = 0 by rewrite rmorphB hVariable hConstants subrr.
have [Q [r [hDivision hRemainder]]]:=@polynomial_field_division K B embed variable coefficient
  hP (variable-embed a) 1%N (polynomial_linear_root_factor_degree a) P.
have hRZero:r = 0.
  case:hRemainder=>[hZero|[d [hD hDegree]]];first exact:hZero.
  have hDZero:d = 0%N by apply/eqP;move:hD;by rewrite ltnS leqn0.
  rewrite hDZero in hDegree.
  have hConstant:=@polynomial_degree_zero_constant K B embed variable coefficient hP r hDegree.
  have hEval:=congr1 E hDivision.
  rewrite hRoot rmorphD rmorphM hLinearZero mulr0 add0r hConstant hConstants in hEval.
  by rewrite hConstant -hEval rmorph0.
exists Q;by rewrite hRZero addr0 in hDivision.
Qed.
(** Source for [polynomial_linear_root_factor_quotient_degree]:
    removing one original linear root factor lowers
    the degree by one; Bourbaki (1990), Chapter IV,
    section 2, no. 1, Proposition 1,
    pp. IV.14–15. Reuse polynomial product degree
    and degree uniqueness from 3.4.7. *)
Theorem polynomial_linear_root_factor_quotient_degree (a:K) (P Q:B) d:
  is_polynomial_degree coefficient P d.+1 ->P = Q*(variable-embed a) ->
    is_polynomial_degree coefficient Q d.
Proof.
move=>hDegree hFactor.
have hPNonzero:=@polynomial_degree_implies_nonzero K B embed variable coefficient hP P d.+1 hDegree.
have hQNonzero:Q<>0 by move=>hZero;apply:hPNonzero;by rewrite hFactor hZero mul0r.
have [m hQDegree]:=@polynomial_degree_exists K B embed variable coefficient hP Q hQNonzero.
have hFieldDomain:is_commutative_integral_domain K.
  move=>x y /eqP;rewrite mulf_eq0;move/orP=>[/eqP hX|/eqP hY];[by left|by right].
have hProduct:=@polynomial_product_degree K B embed variable coefficient hP hFieldDomain
  Q (variable-embed a) m 1%N hQDegree (polynomial_linear_root_factor_degree a).
rewrite -hFactor in hProduct.
have hEqual:=@polynomial_degree_unique K B coefficient P (m+1)%N d.+1 hProduct hDegree.
have hM:m = d by have h:=congr1 predn hEqual;by rewrite addn1 /= in h.
by rewrite -hM.
Qed.
End Factor.
