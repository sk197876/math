(** Federer 2.10.19(3)-(5), p. 181: transfer an already proved
    containing-generator enlargement to a real-power diameter gauge.
    Only its public geometric laws are used; no centre or radius is
    selected and no enlargement is constructed again. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealPower RealPowerPositiveLipschitz MetricRealPowerCost
  MetricDiameterUP MetricDiameter CaratheodoryWeakEnlargementUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_real_power_cost_positive_scale]: supporting
    scalar connection for Federer 2.10.19(3)-(5), p. 181, from the
    real-degree gauge of 2.10.2, p. 171. Positive finite diameter
    scaling multiplies cost by its real power, including zero and
    infinite diameters and degree zero. *)
Lemma metric_real_power_cost_positive_scale (R : realType) (a p k : R)
    (d : \bar R) :
    (0<k)%R -> 0<=d ->
    metric_real_power_cost a p (k%:E*d)=
      (real_power k p)%:E*metric_real_power_cost a p d.
Proof.
move=> hk hd; rewrite /metric_real_power_cost
  (@extended_metric_real_power_positive_scale R k p d hk hd).
by rewrite muleCA.
Qed.

(** Source for [weak_enlargement_transfer_real_power]: supporting
    real-degree connection for Federer 2.10.19(3)-(5), p. 181. Keep
    an existing containing generator and its diameter control k. The
    real power gauge satisfies the same weak enlargement laws with
    control max(k,k^p). Reuse the existing member, containment and
    diameter laws, and only transfer the scalar cost estimate. *)
Theorem weak_enlargement_transfer_real_power (R : realType) (X : metricType R)
    (F : set (set X)) (c : set X -> \bar R) (E : set X -> set X)
    (k a p : R) :
    is_weak_caratheodory_enlargement F c E k ->
    (0<=a)%R -> (0<=p)%R ->
    is_weak_caratheodory_enlargement F (@metric_real_diameter_cost R X a p) E
      (Order.max k (real_power k p)).
Proof.
move=> hE ha hp.
pose K := Order.max k (real_power k p).
have hk := weak_enlargement_constant_positive hE.
have hkK : (k<=K)%R by rewrite /K le_max lexx.
have hpowerK : (real_power k p<=K)%R by rewrite /K le_max lexx orbT.
have hkKE : k%:E<=K%:E by rewrite lee_fin.
have hpKE : (real_power k p)%:E<=K%:E by rewrite lee_fin.
constructor.
- exact: lt_le_trans hk hkK.
- move=> S hS; exact: (@metric_real_power_cost_nonnegative R a p (extended_metric_diameter S) ha).
- exact: weak_enlargement_member hE.
- exact: weak_enlargement_contains hE.
- move=> S hS.
  have hd := metric_diameter_nonnegative (extended_metric_diameter_specification S).
  exact: le_trans (weak_enlargement_diameter hE hS) (lee_wpmul2r hd hkKE).
- move=> S hS.
  have hd := metric_diameter_nonnegative (extended_metric_diameter_specification S).
  have he := metric_diameter_nonnegative (extended_metric_diameter_specification (E S)).
  have hb := @metric_real_power_cost_monotone R a p _ _ ha hp he
    (weak_enlargement_diameter hE hS).
  rewrite (@metric_real_power_cost_positive_scale R a p k _ hk hd) in hb.
  have hc : 0<=metric_real_diameter_cost a p S :=
    @metric_real_power_cost_nonnegative R a p (extended_metric_diameter S) ha.
  exact: le_trans hb (lee_wpmul2r hc hpKE).
Qed.
