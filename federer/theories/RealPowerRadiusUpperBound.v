(** Federer 2.10.19(1)-(2), p. 181: extend a small-positive-radius power
    bound to radius zero. Reuse the proved small-enlargement law of the
    real power gauge, including degree zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal
  topology lra.
From Federer Require Import RealPower RealPowerGaugeEnlargement ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [real_power_positive_radius_upper_at_zero]: supporting
    radius-zero passage in Federer 2.10.19(1)-(2), p. 181. A fixed
    extended value bounded by every sufficiently small positive-radius
    real power is bounded by its value at zero. Reuse real-power gauge
    continuity through its already proved small-enlargement law. *)
Lemma real_power_positive_radius_upper_at_zero (R : realType) (x : \bar R)
    (a e p : R) :
    (0<a)%R -> (0<e)%R -> (0<=p)%R ->
    (forall r : R, (0<r<e)%R -> x<=(a*real_power r p)%R%:E) ->
    x<=(a*real_power 0%R p)%R%:E.
Proof.
move=> ha he hp hbound.
rewrite leNgt; apply/negP=> hbad.
have [q [hq hqx]] := @extended_rationals_order_dense R
  (a*real_power 0%R p)%R%:E x hbad.
have hb : (a*real_power 0%R p<ratr q)%R by move: hq; rewrite lte_fin.
have [r [hr [hcap hcost]]] := @real_power_gauge_small_enlargement R
  a p 0%R e (ratr q) ha hp (lexx 0%R) he hb.
have hsmall : (0<r+r<e)%R.
  apply/andP; split; first by lra.
  by rewrite add0r in hcap.
have h := hbound (r+r)%R hsmall.
rewrite add0r in hcost.
have hh : x<(ratr q : R)%:E.
  apply: le_lt_trans h _; by rewrite lte_fin.
by have := lt_trans hqx hh; rewrite ltxx.
Qed.
