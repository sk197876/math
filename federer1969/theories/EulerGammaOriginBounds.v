(** Federer (1969), 3.2.13, p. 250: scalar
    estimates at zero for the defining Gamma integral.
    Nonpositive powers on positive bases are handled by
    their actual order law, not by continuity at zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import EulerGammaUP RealPower RealPowerSuccessor RealPowerDivision
  RealExponentialUP RealExponentialSealed RealExponentialLaws FlatExponentialPowerBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [gamma_nonpositive_power_base_order]:
    supporting domination of x^(s-1) near zero in
    Federer 3.2.13, p. 250, when 0<s<= 1. *)
Lemma gamma_nonpositive_power_base_order (R:realType) (x y p:R):
  0<x ->0<y ->p<= 0 ->x<=y ->real_power y p<=real_power x p.
Proof.
move=>hx hy hp hxy.
rewrite !real_power_positive_base // real_exponential_order.
have hLog:RealExponential.logarithm x<=RealExponential.logarithm y.
  by rewrite real_logarithm_order.
exact (ler_wnM2l hp hLog).
Qed.

(** Source for [gamma_integrand_exponential_upper]: the
    bound exp(-x)<= 1 on the positive domain of the
    Gamma integral, Federer 3.2.13, p. 250. *)
Lemma gamma_integrand_exponential_upper (R:realType) (s x:R):
  0<x ->euler_gamma_integrand s x<=real_power x (s-1).
Proof.
move=>hx.
have hExp:RealExponential.exponential (-x)<= 1.
  rewrite -(real_exponential_zero (@RealExponential.laws R)) real_exponential_order; lra.
have hh:=ler_wpM2r (real_power_nonnegative x (s-1)) hExp.
by rewrite mul1r in hh.
Qed.

(** Source for [gamma_small_exponent_interval_cost]: the
    dyadic near-zero cost bound proving finiteness of
    Gamma(s) for 0<s<= 1, Federer 3.2.13,
    p. 250. A positive interval scale r times
    the integrand at x>=r/2 is at most 2^(1-s) r^s. *)
Lemma gamma_small_exponent_interval_cost (R:realType) (s r x:R):
  0<s ->s<= 1 ->0<r ->r/2<=x ->
  r*euler_gamma_integrand s x<=real_power 2 (1-s)*real_power r s.
Proof.
move=>hs hs1 hr hLow.
have hTwo:(0:R)<2 by lra.
have hHalf:0<r/2:=divr_gt0 hr hTwo.
have hx:0<x:=lt_le_trans hHalf hLow.
have hP:s-1<= 0 by lra.
have hPower:=gamma_nonpositive_power_base_order hHalf hx hP hLow.
have hBound:=ler_wpM2l (ltW hr) (le_trans (gamma_integrand_exponential_upper s hx) hPower).
apply:le_trans hBound _.
have hR:=@real_power_add_exponents_positive R r (s-1) 1 hr.
rewrite subrK (real_power_one_exponent (ltW hr)) in hR.
have hNeg:real_power 2 (1-s)=(real_power 2 (s-1))^-1.
  rewrite !real_power_positive_base //.
  have hOpp:(1-s)*RealExponential.logarithm (2:R)= -((s-1)*RealExponential.logarithm (2:R)) by ring.
  by rewrite hOpp real_exponential_negative_inverse.
rewrite (@real_power_division R r 2 (s-1) (ltW hr) hTwo) hNeg.
have hEquality:r*(real_power r (s-1)/real_power 2 (s-1))=
    (real_power 2 (s-1))^-1*real_power r s.
  rewrite hR; ring.
by rewrite hEquality.
Qed.

(** Source for [gamma_power_of_natural_base]: the
    dyadic geometric-series calculation for Gamma finiteness,
    Federer 3.2.13, p. 250. Valid for
    any real exponent and nonnegative base, with 0^0= 1. *)
Lemma gamma_power_of_natural_base (R:realType) (a p:R) n:
  0<=a ->real_power (a^+n) p=(real_power a p)^+n.
Proof.
move=>ha; elim:n=>[|n ih].
- by rewrite !expr0 real_power_one_base.
- rewrite exprS real_power_product // ?exprn_ge0 // ih; by rewrite exprS.
Qed.

(** Source for [gamma_positive_base_exponent_order_below_one]:
    exponent comparison on 0<x<=1 supporting Gamma's
    origin bound, Federer 3.2.13, p. 250.
    Exponents may be negative because the base is strictly positive. *)
Lemma gamma_positive_base_exponent_order_below_one (R:realType) (x p q:R):
  0<x ->x<= 1 ->p<=q ->real_power x q<=real_power x p.
Proof.
move=>hx hx1 hpq.
have hLog:RealExponential.logarithm x<= 0.
  by rewrite -(real_logarithm_one R) real_logarithm_order //.
rewrite !real_power_positive_base // real_exponential_order.
nra.
Qed.

(** Source for [gamma_origin_comparison]: domination by
    any smaller positive Gamma parameter on 0<x<=1,
    supporting the finite defining integral of Federer
    3.2.13, p. 250. *)
Lemma gamma_origin_comparison (R:realType) (p s x:R):
  0<x ->x<= 1 ->p<=s ->euler_gamma_integrand s x<=euler_gamma_integrand p x.
Proof.
move=>hx hx1 hps; apply:ler_wpM2l.
- exact:ltW (real_exponential_positive (@RealExponential.laws R) (-x)).
- apply:gamma_positive_base_exponent_order_below_one=> //; lra.
Qed.
