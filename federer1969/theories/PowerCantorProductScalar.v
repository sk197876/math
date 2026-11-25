(** Federer (1969), 2.10.29, p. 194: scalar power comparisons in the two
    product estimates. These supporting lemmas prove the small factor
    d^(1/j)/r<=1 from d<=r^j, then compare exponents using k+1/j<=m+1. They
    include k=0 for positive test diameters. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealPower RealPowerSuccessor RealPowerExponentOrder
  RealExponentialUP RealExponentialSealed RealExponentialLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_power_natural_positive_base]: supporting
    agreement of real and natural powers in
    d<=r^j in 2.10.29, p. 194.
    Only positive bases are needed here. *)
Lemma real_power_natural_positive_base (R : realType) (x : R) : 0<x ->
  forall n, real_power x n%:R=x^+n.
Proof.
move=> hx; elim=> [|n ih]; first by rewrite real_power_zero_exponent expr0.
rewrite -addn1 natrD real_power_add_exponents_positive // ih.
by rewrite real_power_one_exponent ?ltW // exprD expr1.
Qed.

(** Source for [real_power_exponent_order_positive_unit_base]: supporting
    exponent comparison on (0,1] in 2.10.29,
    p. 194. A positive base permits zero
    exponents as well as arbitrary real exponents. *)
Lemma real_power_exponent_order_positive_unit_base (R : realType) (x p q : R) :
  0<x -> x<=1 -> p<=q -> real_power x q<=real_power x p.
Proof.
move=> hx hx1 hpq.
have hlog : RealExponential.logarithm x<=0.
  by rewrite -(real_logarithm_one R) real_logarithm_order.
rewrite !real_power_positive_base // real_exponential_order.
exact (ler_wnM2r hlog hpq).
Qed.

(** Source for [power_cantor_product_scale_bound]: direct scalar
    estimate common to both cases of 2.10.29,
    p. 194: if d<=r^j and k+1/j<=m+1,
    then d^(m+1)*r^m/r<=d^k*r^m.
    Strictly positive d and r make division
    legitimate; zero diameters are treated separately
    in the measure argument. *)
Lemma power_cantor_product_scale_bound (R : realType) (d r m k : R) j :
  0<d -> d<=1 -> 0<r ->
  d<=r^+j.+1 -> k+(j.+1%:R)^-1<=m+1 ->
  real_power d (m+1)*real_power r m/r<=real_power d k*real_power r m.
Proof.
move=> hd hd1 hr hsmall hexp.
have hJ : (0<j.+1%:R :> R) by rewrite ltr0n.
have hi : (0<(j.+1%:R : R)^-1) by rewrite invr_gt0.
have hroot : real_power d (j.+1%:R)^-1<=r.
  have hh := real_power_monotone (ltW hd) hsmall hi.
  have heq : real_power (r^+j.+1) (j.+1%:R)^-1=r.
    rewrite -(@real_power_natural_positive_base R r hr j.+1).
    exact: real_power_root_cancel (ltW hr) hJ.
  by rewrite heq in hh.
have he := @real_power_exponent_order_positive_unit_base R d _ _ hd hd1 hexp.
rewrite (@real_power_add_exponents_positive R d k _ hd) in he.
have hle : real_power d (m+1)<=real_power d k*r.
  exact (le_trans he (ler_wpM2l (real_power_nonnegative d k) hroot)).
have hrinv : 0<=r^-1 by rewrite invr_ge0; exact: ltW hr.
have hcost := ler_wpM2r (mulr_ge0 (real_power_nonnegative r m) hrinv) hle.
rewrite !mulrA in hcost.
have hcancel : real_power d k*r*real_power r m/r=real_power d k*real_power r m.
  by rewrite [real_power d k*r*real_power r m]mulrAC mulfK ?gt_eqF.
by rewrite hcancel in hcost.
Qed.
