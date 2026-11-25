(** Federer (1969), 3.2.13, p. 250: pointwise
    dyadic majorants for the defining Gamma integral.
    All exponents and interval boundaries are explicit;
    no finite-integrability hypothesis is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra ring.
From Federer Require Import EulerGammaUP EulerGammaBounds EulerGammaOriginBounds GammaDyadicIntervals
  RealPower RealPowerDivision RealPowerContinuity RealExponentialSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [gamma_dyadic_origin_upper]: a constant
    upper bound on each near-zero dyadic interval,
    establishing the defining Gamma integral in Federer
    3.2.13, p. 250. The smaller exponent p
    is positive, at most one and no larger than s. *)
Lemma gamma_dyadic_origin_upper (R:realType) (s p x:R) n:
  0<p ->p<= 1 ->p<=s ->gamma_origin_interval n x ->
  euler_gamma_integrand s x<=
    real_power 2 (1-p)*(real_power (1/2) p)^+n/(1/2)^+n.
Proof.
move=>hp hp1 hps [hLow hHigh].
have hHalf:(0<(1/2:R)) by apply:divr_gt0; lra.
have hHalf1:((1/2:R)<= 1) by lra.
have hr:0<(1/2:R)^+n:=exprn_gt0 n hHalf.
have hSmall:((1/2:R)^+n<= 1):=exprn_ile1 n (ltW hHalf) hHalf1.
have hTwo:(0<(2:R)) by lra.
have hx:0<x:=lt_le_trans (divr_gt0 hr hTwo) hLow.
have hx1:x<= 1:=le_trans hHigh hSmall.
have hComp:=gamma_origin_comparison hx hx1 hps.
have hOrigin:=gamma_small_exponent_interval_cost hp hp1 hr hLow.
have hBound:=le_trans (ler_wpM2l (ltW hr) hComp) hOrigin.
rewrite gamma_power_of_natural_base ?(ltW hHalf) // in hBound.
rewrite ler_pdivlMr // mulrC; exact hBound.
Qed.

(** Source for [gamma_dyadic_tail_upper]: the
    polynomial-exponential tail estimate on an actual
    dyadic interval, supporting Gamma finiteness in
    Federer 3.2.13, p. 250. *)
Lemma gamma_dyadic_tail_upper (R:realType) k (s x:R) n:
  s<=k.+1%:R ->gamma_tail_interval n x ->
  euler_gamma_integrand s x<=
    (k.+2%:R:R)^+k.+2*((2^+n)^-1)^+2.
Proof.
move=>hs [hLow hHigh].
have hTwo:(0<(2:R)) by lra.
have hr:0<(2:R)^+n:=exprn_gt0 n hTwo.
have hPower1 j:((1:R)<=2^+j).
  elim:j=>[|j ih]; first by rewrite expr0.
  rewrite exprS; have hj:0<=(2:R)^+j:=exprn_ge0 j (ltW hTwo); nra.
have hr1:=hPower1 n.
have hx1:1<=x:=le_trans hr1 hLow.
have hx:0<x:=lt_le_trans ltr01 hx1.
have hInv:0<=x^-1 by rewrite invr_ge0; exact:ltW hx.
have hInvBound:x^-1<=(2^+n)^-1 by rewrite lef_pV2.
have hSq:(x^-1)^+2<=((2^+n)^-1)^+2.
  rewrite !expr2; exact (ler_pM hInv hInv hInvBound hInvBound).
apply:le_trans (euler_gamma_integrand_tail_bound hs hx1) _.
apply:ler_wpM2l=> //; apply:exprn_ge0; exact:ler0n.
Qed.
