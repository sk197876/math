(** Federer (1969), 2.10.29, p. 195: scalar powers supporting finite
    Cartesian products of local density estimates and finite cube covers. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealPower RealPowerSuccessor PowerCantorProductScalar.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_power_nonnegative_exponents_add]: supporting
    addition of the nonnegative local exponents
    in 2.10.29, p. 195, including a
    zero base and either zero exponent. *)
Lemma real_power_nonnegative_exponents_add (R : realType) (x p q : R) :
  0<=x -> 0<=p -> 0<=q ->
  real_power x (p+q)=real_power x p*real_power x q.
Proof.
move=> hx hp hq.
have [hp0|hpne] := eqVneq p 0.
- by rewrite hp0 add0r real_power_zero_exponent mul1r.
have [hq0|hqne] := eqVneq q 0.
- by rewrite hq0 addr0 real_power_zero_exponent mulr1.
have hpp : 0<p by rewrite lt_neqAle eq_sym hpne hp.
have hqp : 0<q by rewrite lt_neqAle eq_sym hqne hq.
have [hx0|hxne] := eqVneq x 0.
- by rewrite hx0 !real_power_zero_base ?gt_eqF ?addr_gt0 // mulr0.
have hxp : 0<x by rewrite lt_neqAle eq_sym hxne hx.
exact: real_power_add_exponents_positive hxp.
Qed.

(** Source for [real_power_positive_natural_multiple]: supporting
    q*m power of a positive side length
    in the Cartesian cube covers of 2.10.29,
    p. 195. Natural q=0 is included. *)
Lemma real_power_positive_natural_multiple (R : realType) (r m : R) :
  0<r -> 0<m -> forall q,
    real_power r (q%:R * m)=(real_power r m)^+q.
Proof.
move=> hr hm [|q]; first by rewrite mul0r real_power_zero_exponent expr0.
have hq : (0<q.+1%:R :> R) by rewrite ltr0n.
have hh := @real_power_positive_iterate R r m q.+1%:R (ltW hr) hm hq.
rewrite mulrC in hh.
rewrite (@real_power_natural_positive_base R (real_power r m) (real_power_strictly_positive _ hr) q.+1) in hh.
exact: esym hh.
Qed.
