(** Federer (1969), 3.4.5, p. 321: actual
    finite polynomial coefficients on the rational cubic cone,
    supporting the example cited to Cartan (1957), pp. 97–99.
    No polynomial division theorem is imported. *)
From mathcomp Require Import all_boot all_order all_algebra ring.
From Federer Require Import DistinctDegreePolynomialIndependence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [shifted_quadratic_coefficient]: actual
    coefficients of t^j*(1+t^2)^m, supporting the real
    polynomial restriction in 3.4.5, p. 321. *)
Definition shifted_quadratic_coefficient (K:fieldType) j m n:K:=
  \sum_(ell<m.+1 | (j+2 * ell==n)%N) (('C(m,ell))%:R:K).

(** Source for [shifted_quadratic_coefficient_monic]: the
    leading coefficient is one at degree j+2m,
    supporting the cubic-cone argument in 3.4.5, p. 321. *)
Lemma shifted_quadratic_coefficient_monic (K:fieldType) j m:
  @shifted_quadratic_coefficient K j m (j+2 * m)%N= 1.
Proof.
rewrite /shifted_quadratic_coefficient big_mkcond (bigD1 ord_max) //= eqxx binn.
have hOthers:(\sum_(ell<m.+1 | ell!=ord_max)
    if (j+2 * ell==j+2 * m)%N then (('C(m,ell))%:R:K) else 0)=0.
  apply:big1=>ell hEll.
  have hDifferent:(j+2 * ell!=j+2 * m)%N.
    rewrite eqn_add2l eqn_mul2l /=.
    by move:hEll;rewrite -val_eqE.
  by rewrite (negbTE hDifferent).
by rewrite hOthers addr0.
Qed.

(** Source for [shifted_quadratic_coefficient_above]: no
    coefficient lies above its actual degree, supporting
    the finite elimination in 3.4.5, p. 321. *)
Lemma shifted_quadratic_coefficient_above (K:fieldType) j m n:
  (j+2 * m<n)%N ->@shifted_quadratic_coefficient K j m n=0.
Proof.
move=>hN;rewrite /shifted_quadratic_coefficient;apply:big1=>ell /eqP hEqual.
have hLe:(j+2 * ell<=j+2 * m)%N.
  rewrite leq_add2l leq_mul2l /=;by have:=ltn_ord ell;rewrite ltnS.
have hImpossible:=leq_trans (leq_add (leqnn 1) hLe) hN.
by rewrite hEqual ltnn in hImpossible.
Qed.

(** Source for [shifted_quadratic_polynomial_expansion]: the
    actual binomial expansion of the restricted monomial,
    supporting the example cited at 3.4.5, p. 321.
    Every upper cutoff above the original degree is retained. *)
Lemma shifted_quadratic_polynomial_expansion (K:fieldType) j m N (t:K):
  (j+2 * m<N)%N ->
  \sum_(n<N) (@shifted_quadratic_coefficient K j m n)*t^+n=
    t^+j*(1+t^+2)^+m.
Proof.
move=>hN;rewrite /shifted_quadratic_coefficient.
have hExpand:(\sum_(n<N) (\sum_(ell<m.+1 | (j+2 * ell==n)%N) (('C(m,ell))%:R:K))*t^+n)=
    \sum_(ell<m.+1) (('C(m,ell))%:R:K)*t^+(j+2 * ell).
  under eq_bigr do rewrite mulr_suml big_mkcond.
  rewrite exchange_big;apply:eq_bigr=>ell _.
  have hDegree:(j+2 * ell<N)%N.
    apply:leq_trans _ hN.
    rewrite ltnS.
    rewrite leq_add2l leq_mul2l /=;by have:=ltn_ord ell;rewrite ltnS.
  pose d:'I_N:=Ordinal hDegree.
  rewrite (bigD1 d) //= eqxx.
  have hOthers:(\sum_(n<N | n!=d)
      if (j+2 * ell==n)%N then (('C(m,ell))%:R:K)*t^+n else 0)=0.
    apply:big1=>n hDifferent.
    have hNe:(j+2 * ell!=n)%N.
      by move:hDifferent;rewrite -val_eqE /d /= eq_sym.
    by rewrite (negbTE hNe).
  by rewrite hOthers addr0.
rewrite hExpand exprDn mulr_sumr.
apply:eq_bigr=>ell _.
rewrite exprD -exprM expr1n mul1r.
ring.
Qed.

(** Source for [shifted_quadratic_polynomials_independent]:
    monomials restricted to the actual rational cone are
    independent whenever their resulting leading degrees are
    distinct, supporting 3.4.5, p. 321. *)
Theorem shifted_quadratic_polynomials_independent (K:fieldType) (h0:[pchar K]=i pred0)
    (V:lmodType K) (I:finType) (j m:I->nat) (a:I->V) N:
  injective (fun i=>(j i+2 * m i)%N) ->
  (forall i,(j i+2 * m i<N)%N) ->
  (forall t,\sum_i (t^+(j i)*(1+t^+2)^+(m i))*:a i=0) ->forall i,a i=0.
Proof.
move=>hInjective hDegree hValues.
apply:(@distinct_degree_polynomials_independent K h0 V I
  (fun i=>(j i+2 * m i)%N) (fun i=>@shifted_quadratic_coefficient K (j i) (m i)) a N
  hInjective hDegree (fun i=>@shifted_quadratic_coefficient_monic K (j i) (m i))
  (fun i n=>@shifted_quadratic_coefficient_above K (j i) (m i) n))=>t.
under eq_bigr do rewrite (shifted_quadratic_polynomial_expansion t (hDegree _)).
exact:hValues.
Qed.
