(** Federer (1969), 3.4.5, p. 321: equality of the
    actual finite quadratic-substitution parameter coefficients
    and the original even/odd remainder coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import QuadraticSubstitutionParameterCoefficients QuadraticFormalRemainder
  FiniteAdditionDeltaSelection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Identity.
Variable K:fieldType.

(** Source for [quadratic_parameter_original_remainder]: the
    original additive index selection and finite zero padding
    identify both original coefficient expressions exactly,
    supporting 3.4.5, p. 321. *)
Theorem quadratic_parameter_original_remainder (a:nat->nat->K) parity N ell:
  (ell<=N)%N ->quadratic_substitution_parameter_coefficient parity N ell
    (fun i k=>a i (2*k+parity)%N)=
    @quadratic_formal_remainder_coefficient K K^o a parity N ell.
Proof.
move=>hEll;rewrite /quadratic_substitution_parameter_coefficient.
under eq_bigr do rewrite big_mkcond.
rewrite exchange_big.
under eq_bigr do rewrite -big_mkcond.
have hRow (k:'I_N.+1):
    (\sum_(i<N.+1 | ((ell<=k)&&(i+2*k+parity+ell==N))%N)
      a i (2*k+parity)%N*('C(k,ell))%:R*(-1)^+(k-ell))=
    if ((ell<=k)&&(2*k+parity<=N-ell))%N then
      a (N-ell-(2*k+parity))%N (2*k+parity)%N*('C(k,ell))%:R*(-1)^+(k-ell) else 0.
  rewrite big_mkcond;case hEK:(ell<=k)%N;last by rewrite /= big1.
  have hTest i:(i+2*k+parity+ell==N)%N=(i+(2*k+parity+ell)==N)%N by rewrite !addnA.
  have hRewrite:(\sum_(i<N.+1) if ((ell<=k)&&(i+2*k+parity+ell==N))%N then
      a i (2*k+parity)%N*('C(k,ell))%:R*(-1)^+(k-ell) else 0)=
    \sum_(i<N.+1 | (i+(2*k+parity+ell)==N)%N)
      a i (2*k+parity)%N*('C(k,ell))%:R*(-1)^+(k-ell).
    rewrite [RHS]big_mkcond;apply:eq_bigr=>i _;by rewrite hEK /= hTest.
  rewrite hEK /= in hRewrite.
  rewrite hRewrite.
  have hSelection:=@finite_addition_delta_selection K^o N (2*k+parity+ell)%N
    (fun i=>a i (2*k+parity)%N*('C(k,ell))%:R*(-1)^+(k-ell)).
  rewrite hSelection.
  have hCondition:(2*k+parity+ell<=N)%N=(2*k+parity<=N-ell)%N by rewrite leq_subRL // addnC.
  have hIndex:(N-(2*k+parity+ell)=N-ell-(2*k+parity))%N by rewrite addnC subnDA.
  by rewrite hCondition hIndex.
under eq_bigr do rewrite hRow.
rewrite -big_mkcond /quadratic_formal_remainder_coefficient.
have hBound:((N-ell).+1<=N.+1)%N by rewrite -[(N-ell).+1]addn1 -[N.+1]addn1 leq_add2r;exact:leq_subr.
have hPadding:=big_ord_widen_cond N.+1
  (fun k=>((ell<=k)&&(2*k+parity<=N-ell))%N)
  (fun k=>a (N-ell-(2*k+parity))%N (2*k+parity)%N*('C(k,ell))%:R*(-1)^+(k-ell)) hBound.
have hFilter k:((ell<=k)&&(2*k+parity<=N-ell))%N ->(k<(N-ell).+1)%N.
  move=>/andP[_ hk];rewrite ltnS;apply:(leq_trans _ hk).
  rewrite mul2n -addnn;exact:leq_trans (leq_addr k k) (leq_addr parity (k+k)).
transitivity (\sum_(k<(N-ell).+1 | ((ell<=k)&&(2*k+parity<=N-ell))%N)
  a (N-ell-(2*k+parity))%N (2*k+parity)%N*('C(k,ell))%:R*(-1)^+(k-ell)).
- symmetry;rewrite hPadding;apply:eq_bigl=>k.
  case hPred:((ell<=k)&&(2*k+parity<=N-ell))%N;last by [].
  by rewrite (hFilter k hPred).
- apply:eq_bigr=>k _.
change (a (N-ell-(2*k+parity))%N (2*k+parity)%N*('C(k,ell))%:R*(-1)^+(k-ell)=
  (('C(k,ell))%:R*(-1)^+(k-ell))*a (N-ell-(2*k+parity))%N (2*k+parity)%N).
by rewrite -mulrA mulrC.
Qed.
End Identity.
