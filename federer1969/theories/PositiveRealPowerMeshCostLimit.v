(** Federer 2.10.45, p. 203: recover the exact real-degree diameter
    cost by decreasing positive meshes, including diameter zero. Reuse
    the proved real-power small-enlargement law of 2.10.2, p. 171. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal lra.
From Federer Require Import RealPower RealPowerGaugeEnlargement ExtendedRealBounds ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [positive_real_power_mesh_cost_limit]: supporting limit
    step for the product generator estimate in Federer 2.10.45, p. 203.
    The real degree may be zero, and the bounded quantity may initially
    be infinite. No second-factor geometric enlargement is assumed. *)
Theorem positive_real_power_mesh_cost_limit (R : realType) (c p d t K : R)
    (x : \bar R) :
  (0 < c)%R -> (0 <= p)%R -> (0 < K)%R -> (0 <= d)%R -> (d < t)%R ->
  (forall h : R, (0 < h)%R -> (d <= h)%R -> (h < t)%R ->
    x <= (K*(c*real_power h p))%R%:E) ->
    x <= (K*(c*real_power d p))%R%:E.
Proof.
move=> hc hp hK hd hdt hbound; rewrite leNgt; apply/negP=> hbad.
have [q [hbq hqx]] := @extended_rationals_order_dense R
  (K*(c*real_power d p))%R%:E x hbad.
have hb : (K*c*real_power d p < ratr q)%R by move: hbq; rewrite lte_fin mulrA.
have [e [he [hcap hcost]]] := @real_power_gauge_small_enlargement R
  (K*c)%R p d t (ratr q) (mulr_gt0 hK hc) hp hd hdt hb.
have hpositive : (0 < d+e+e)%R by lra.
have hde : (d <= d+e+e)%R by lra.
have h := hbound (d+e+e)%R hpositive hde hcap.
have hlt : x < (ratr q : R)%:E.
  apply: le_lt_trans h _; rewrite lte_fin mulrA; exact: hcost.
by have hf := lt_trans hqx hlt; rewrite ltxx in hf.
Qed.
