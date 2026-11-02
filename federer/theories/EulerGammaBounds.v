(** Federer (1969), 3.2.13, p. 250: scalar
    bounds proving existence of the defining Gamma integral.
    Tail estimates use only the project's opaque exponential
    laws and their proved polynomial decay. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra ring.
From Federer Require Import EulerGammaUP RealPower RealPowerExponentOrder RealExponentialUP
  RealExponentialSealed RealExponentialLaws FlatExponentialPowerBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euler_gamma_integrand_positive]: positivity
    of the integrand defining Gamma in Federer 3.2.13,
    p. 250, at every positive integration variable. *)
Lemma euler_gamma_integrand_positive (R:realType) (s x:R):
  0<x ->0<euler_gamma_integrand s x.
Proof.
move=>hx; apply:mulr_gt0.
- exact (real_exponential_positive (@RealExponential.laws R) (-x)).
- exact (real_power_strictly_positive (s-1) hx).
Qed.

(** Source for [euler_gamma_natural_power]: supporting
    scalar identification for the finite polynomial tail
    bound of the Gamma integral, Federer 3.2.13, p. 250. *)
Lemma euler_gamma_natural_power (R:realType) (x:R) n:
  0<x ->real_power x n%:R=x^+n.
Proof.
move=>hx; rewrite real_power_positive_base // real_exponential_natural_multiple.
by rewrite (real_exponential_logarithm (@RealExponential.laws R)).
Qed.

(** Source for [euler_gamma_integrand_tail_bound]: a
    proved integrable-tail estimate for the defining Gamma
    integral of Federer 3.2.13, p. 250.
    Choose k+1>=s; the integrand on x>= 1 is
    bounded by (k+2)^(k+2) x^-2. *)
Lemma euler_gamma_integrand_tail_bound (R:realType) k (s x:R):
  s<=(k.+1%:R:R) ->1<=x ->
  euler_gamma_integrand s x<=(k.+2%:R:R)^+k.+2*(x^-1)^+2.
Proof.
move=>hs hx.
have hxPos:0<x:=lt_le_trans ltr01 hx.
have hxNe:x!= 0:=lt0r_neq0 hxPos.
have hCast:((k.+1)%:R:R)=k%:R+1 by rewrite -addn1 natrD.
have hExponent:s-1<=(k%:R:R) by rewrite hCast in hs; lra.
have hPower:=@real_power_exponent_order_above_one R x (s-1) k%:R hx hExponent.
rewrite (euler_gamma_natural_power k hxPos) in hPower.
have hExp:=@real_exponential_negative_power_upper R k.+2 x (ltn0Sn k.+1) hxPos.
have hProduct:=ler_wpM2r (real_power_nonnegative x (s-1)) hExp.
have hRatio:0<=(k.+2%:R:R)/x.
  apply:divr_ge0; first exact:ler0n.
  exact:ltW hxPos.
have hPoly:=ler_wpM2l (exprn_ge0 k.+2 hRatio) hPower.
apply:le_trans (le_trans hProduct hPoly) _.
have hCancel:(x^-1)^+k*x^+k= 1 by rewrite -exprMn mulVf // expr1n.
have hFactor:((k.+2%:R:R)/x)^+k.+2*x^+k=
    (k.+2%:R:R)^+k.+2*((x^-1)^+k*x^+k)*(x^-1)^+2.
  have hSplit:(x^-1)^+k.+2=(x^-1)^+k*(x^-1)^+2 by rewrite -exprD addn2.
  rewrite exprMn hSplit; ring.
by rewrite hFactor hCancel mulr1.
Qed.
