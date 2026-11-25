(** Federer (1969), 2.4.12, p. 87: identify the (p+1)-st root of the
    powered-norm integral with the p/(p+1)-st power of its Lp norm.
    Supporting scalar laws include zero and positive infinity. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import RealPower ExtendedPositivePower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [extended_positive_power_iterate]: supporting
    exponent multiplication for the gauge formula of Federer
    2.4.12, p. 87. Only positive exponents and
    nonnegative extended arguments are used. *)
Lemma extended_positive_power_iterate (R : realType) (x : \bar R) (p q : R) :
  0 <= x -> (0 < p)%R -> (0 < q)%R ->
  extended_positive_power (extended_positive_power x p) q =
    extended_positive_power x (p*q)%R.
Proof.
case: x=> [x| |] //=; rewrite lee_fin=> hx hp hq.
by rewrite real_power_positive_iterate.
Qed.

(** Source for [extended_power_root_gauge_identity]: the
    equality of the two expressions for r in Federer
    2.4.12, p. 87, after choosing r^(p+1)
    equal to the integral of |f|^p. *)
Lemma extended_power_root_gauge_identity (R : realType) (x : \bar R) (p : R) :
  0 <= x -> (0 < p)%R ->
  extended_positive_power (extended_positive_power x p^-1) (p/(p+1))%R =
    extended_positive_power x (p+1)^-1.
Proof.
move=> hx hp.
have hp1 : (0 < p+1)%R := addr_gt0 hp ltr01.
have hi : (0 < p^-1)%R by rewrite invr_gt0.
have hq : (0 < p/(p+1))%R by rewrite divr_gt0.
rewrite (@extended_positive_power_iterate R x p^-1 (p/(p+1))%R hx hi hq).
by rewrite mulrA mulVf ?gt_eqF // mul1r.
Qed.
