(** Federer (1969), 2.4.15, proof p. 89: the elementary bound (x+y)^p <=
    2^p(x^p+y^p) for nonnegative scalars, used to establish summability of
    the sum before applying Holder. These supporting scalar estimates are
    proved from the project's real-power laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealPower RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_power_sum_bound]: the second scalar inequality in the
    opening proof of Federer 2.4.15, p. 89 The supporting estimate holds for
    every positive exponent, a strengthening of its printed application with
    p>1. *)
Lemma real_power_sum_bound (R : realType) (p x y : R) :
  0 < p -> 0 <= x -> 0 <= y ->
  real_power (x+y) p <= real_power 2 p * (real_power x p+real_power y p).
Proof.
move=> hp hx hy.
have htwo : 0 <= (2 : R) by rewrite ler0n.
have hxy : 0 <= x+y := addr_ge0 hx hy.
have [hle|hle] := leP x y.
- have hsum : x+y <= 2*y by rewrite mulr_natl mulr2n; exact: lerD hle (lexx y).
  apply: le_trans (@real_power_monotone R (x+y) (2*y) p hxy hsum hp) _.
  rewrite (@real_power_product R 2 y p htwo hy).
  apply: ler_wpM2l; first exact: real_power_nonnegative.
  by rewrite lerDr real_power_nonnegative.
- have hsum : x+y <= 2*x by rewrite mulr_natl mulr2n; exact: lerD (lexx x) (ltW hle).
  apply: le_trans (@real_power_monotone R (x+y) (2*x) p hxy hsum hp) _.
  rewrite (@real_power_product R 2 x p htwo hx).
  apply: ler_wpM2l; first exact: real_power_nonnegative.
  by rewrite lerDl real_power_nonnegative.
Qed.

(** Source for [norm_sum_power_bound]: both pointwise estimates in the
    opening proof of Federer 2.4.15, p. 89 The abstract norm triangle law is
    followed by the scalar power-sum bound. *)
Lemma norm_sum_power_bound (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (p : R) (x y : V) :
  0 < p -> real_power (N (x+y)) p <=
    real_power 2 p * (real_power (N x) p+real_power (N y) p).
Proof.
move=> hp.
apply: le_trans (@real_power_monotone R (N (x+y)) (N x+N y) p
  (real_seminorm_nonnegative hN.1 _) (real_seminorm_triangle hN.1 _ _) hp) _.
exact (@real_power_sum_bound R p (N x) (N y) hp
  (real_seminorm_nonnegative hN.1 x) (real_seminorm_nonnegative hN.1 y)).
Qed.
