(** Federer (1969), 3.4.6, p. 323: the
    original shifted derivative coefficients have the printed
    two-variable positive geometric majorant. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import FactorialExponentialBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_shifted_term_bound]: the
    original factor (i+s)!/(i!s!) is at most 2^(i+s),
    giving the termwise majorant alpha*(2 beta)^s*
    (2 beta |t|)^i*(gamma rho)^j in 3.4.6,
    p. 323. No shifted convergence or analytic
    realisation is assumed. *)
Theorem weierstrass_shifted_term_bound (R:realType) (alpha beta gamma rho t:R)
    (q:nat->nat->R):
  0<alpha ->0<beta ->0<gamma ->0<=rho ->
  (forall i j,`|q i j|<=alpha*beta^+i*gamma^+j*rho^+j) ->
  forall s i j,`|('C(s+i,s))%:R*t^+i*q (s+i)%N j|<=
    alpha*(2*beta)^+s*(2*beta*`|t|)^+i*(gamma*rho)^+j.
Proof.
move=>hAlpha hBeta hGamma hRho hQ s i j.
rewrite !normrM normr_nat normrX.
have hBinomial:(('C(s+i,s))%:R:R)<=(2:R)^+(s+i).
  rewrite -natrX ler_nat;exact:binomial_power_two_bound.
have hPower:0<=`|t|^+i:=exprn_ge0 i (normr_ge0 t).
have hCoefficient:0<=alpha*beta^+(s+i)*gamma^+j*rho^+j:=
  mulr_ge0 (mulr_ge0 (mulr_ge0 (ltW hAlpha) (exprn_ge0 _ (ltW hBeta)))
    (exprn_ge0 j (ltW hGamma))) (exprn_ge0 j hRho).
have hFirst:=ler_wpM2l (mulr_ge0 (ler0n R ('C(s+i,s))) hPower) (hQ (s+i)%N j).
have hSecond:=ler_wpM2r hCoefficient (ler_wpM2r hPower hBinomial).
apply:le_trans hFirst _;apply:le_trans hSecond _.
have hIdentity:(2:R)^+(s+i)*`|t|^+i*(alpha*beta^+(s+i)*gamma^+j*rho^+j)=
    alpha*(2*beta)^+s*(2*beta*`|t|)^+i*(gamma*rho)^+j.
  by rewrite !exprD !exprMn;ring.
by rewrite hIdentity.
Qed.
