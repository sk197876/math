(** Federer (1969), 3.4.7, p. 325: every polynomial
    is its finite coefficient expression. This follows only
    from the independent coefficient laws, not the construction. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialBasicLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section FiniteSums.
Variables A B:comNzRingType.
Variable embed:{rmorphism A->B}.
Variable variable:B.
Variable coefficient:B->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.

(** Source for [polynomial_coefficient_sum]: coefficients
    commute with finite addition, supporting the extension
    in 3.4.7, p. 325. *)
Lemma polynomial_coefficient_sum (I:Type) (r:seq I) (F:I->B) n:
  coefficient (\sum_(i<-r) F i) n = \sum_(i<-r) coefficient (F i) n.
Proof.
elim:r=>[|i r ih].
- rewrite !big_nil;exact:(@polynomial_coefficient_zero A B embed variable coefficient hP n).
- by rewrite !big_cons (@polynomial_coefficient_add A B embed variable coefficient hP) ih.
Qed.

(** Source for [polynomial_finite_expression_coefficient]:
    the coefficient of a finite scalar expression is
    the prescribed scalar inside its range and zero
    outside, supporting 3.4.7, p. 325. *)
Lemma polynomial_finite_expression_coefficient N (f:nat->A) n:
  coefficient (\sum_(i<N) embed (f i)*variable^+i) n =
    if (n<N)%N then f n else 0.
Proof.
rewrite polynomial_coefficient_sum.
under eq_bigr do rewrite (@polynomial_monomial_coefficient A B embed variable coefficient hP).
case:(ltnP n N)=>hN.
- pose index:'I_N:=Ordinal hN.
  rewrite (bigD1 index) //= eqxx.
  rewrite big1 ?addr0 // =>i hi.
  have hNi:(n==(i:nat)) = false.
    apply/negP=>/eqP h;move:hi;by rewrite -val_eqE /= h eqxx.
  by rewrite hNi.
- apply:big1=>i _.
  have hNi:(n==(i:nat)) = false.
    apply/negP=>/eqP h;have hi:=ltn_ord i.
    move:hi;by rewrite -h (leq_gtF hN).
  by rewrite hNi.
Qed.

(** Source for [polynomial_finite_expression]: the polynomial
    extension consists exactly of finite expressions in
    the variable with original coefficients, as used
    in 3.4.7, p. 325. *)
Theorem polynomial_finite_expression (P:B) N:
  (forall i,(N<=i)%N ->coefficient P i = 0) ->
  P = \sum_(i<N) embed (coefficient P i)*variable^+i.
Proof.
move=>hSupport;apply:(@polynomial_coefficients_unique A B embed variable coefficient hP)=>i.
rewrite polynomial_finite_expression_coefficient.
case:(ltnP i N)=>hI;first by [].
exact:hSupport i hI.
Qed.

(** Source for [polynomial_interpolation_exists]: every actual
    finite scalar coefficient function determines a polynomial,
    supporting the transcendental extension in 3.4.7, p. 325. *)
Theorem polynomial_interpolation_exists (f:nat->A):
  (exists N,forall i,(N<=i)%N ->f i = 0) ->
  exists P:B,forall i,coefficient P i = f i.
Proof.
move=>[N hN];exists (\sum_(i<N) embed (f i)*variable^+i)=>i.
rewrite polynomial_finite_expression_coefficient.
case:(ltnP i N)=>hI;first by [].
by rewrite hN.
Qed.
End FiniteSums.
