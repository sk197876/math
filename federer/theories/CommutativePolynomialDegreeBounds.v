(** Federer (1969), 3.4.7, p. 325: finite degree
    bounds supporting polynomial division in the Gauss argument.
    Each bound follows from actual coefficient equations. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialBasicLaws
  CommutativePolynomialDegreeUP CommutativePolynomialDegree.
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

(** Source for [polynomial_degree_implies_nonzero]: a nonzero
    leading coefficient makes the polynomial nonzero,
    supporting 3.4.7, p. 325. *)
Lemma polynomial_degree_implies_nonzero (P:B) n:
  is_polynomial_degree coefficient P n ->P<>0.
Proof.
move=>[hLeading _] hZero;apply:hLeading;rewrite hZero.
exact:(@polynomial_coefficient_zero A B embed variable coefficient hP n).
Qed.

(** Source for [polynomial_degree_below_support_bound]: a
    nonzero polynomial with all coefficients of index
    at least N zero has degree below N,
    supporting division in 3.4.7, p. 325. *)
Lemma polynomial_degree_below_support_bound (P:B) n N:
  is_polynomial_degree coefficient P n ->
  (forall i,(N<=i)%N ->coefficient P i = 0) ->(n<N)%N.
Proof.
move=>[hLeading _] hBound;case:(ltnP n N)=>h;first by [].
exfalso;exact:hLeading (hBound n h).
Qed.

(** Source for [polynomial_degree_zero_constant]: degree-zero
    polynomials are exactly their original constant coefficient,
    supporting the scalar base of 3.4.7, p. 325. *)
Lemma polynomial_degree_zero_constant (P:B):
  is_polynomial_degree coefficient P 0%N ->P = embed (coefficient P 0%N).
Proof.
move=>[_ hHigher];apply:(@polynomial_coefficients_unique A B embed variable coefficient hP)=>i.
rewrite (@polynomial_coefficient_constant A B embed variable coefficient hP).
case:i=>[|i];first by [].
exact:hHigher i.+1 (ltn0Sn i).
Qed.

(** Source for [polynomial_subtract_coefficients]: subtraction
    subtracts original coefficients, supporting leading-term
    cancellation in 3.4.7, p. 325. *)
Lemma polynomial_subtract_coefficients (P Q:B) i:
  coefficient (P-Q) i = coefficient P i-coefficient Q i.
Proof.
by rewrite (@polynomial_coefficient_add A B embed variable coefficient hP)
  (@polynomial_coefficient_opp A B embed variable coefficient hP).
Qed.

(** Source for [polynomial_cancelled_leading_bound]: cancelling
    equal leading coefficients of two degree-bounded polynomials
    leaves all coefficients from that degree onward zero,
    supporting the division step in 3.4.7, p. 325. *)
Lemma polynomial_cancelled_leading_bound (P Q:B) n:
  (forall i,(n<i)%N ->coefficient P i = 0) ->
  (forall i,(n<i)%N ->coefficient Q i = 0) ->
  coefficient P n = coefficient Q n ->
  forall i,(n<=i)%N ->coefficient (P-Q) i = 0.
Proof.
move=>hPHigh hQHigh hEqual i hi;rewrite polynomial_subtract_coefficients.
case:(eqVneq i n)=>[->|hDifferent];first by rewrite hEqual subrr.
have hStrict:(n<i)%N by rewrite ltn_neqAle eq_sym hDifferent hi.
by rewrite hPHigh // hQHigh // subrr.
Qed.
End Bounds.
