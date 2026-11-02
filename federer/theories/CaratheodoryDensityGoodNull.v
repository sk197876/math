(** Federer (1969), 2.10.17(3), p. 179, proof: phi_delta
    B(phi_delta,1-delta,delta) is bounded by (1-delta) times itself and is
    finite, so it is zero. Intersection closure identifies the local
    phi_delta and phi_infinity costs. Passing through all small cutoffs
    gives zero final measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MetricDiameter MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleEnvelopeLaws
  MetricScaleLocalAgreement CaratheodoryLimitUP CaratheodoryDensityGoodSets FiniteMeasureSelfContraction
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_density_good_set_small_scale_zero]: supporting
    finite self-contraction step in 2.10.17(3), p. 179 A fixed threshold t
    in (0,1) is allowed independently of the small cutoff, expanding the
    printed diagonal choice. *)
Theorem caratheodory_density_good_set_small_scale_zero (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (c : J -> \bar R)
    (omega : set X -> \bar R) (A : set X) (t : R) (eta delta : \bar R) :
  (forall j, 0<=c j) -> is_intersection_cost_family S c ->
  is_metric_scale_envelope S c +oo omega -> (0<t<1)%R -> delta<=eta ->
  metric_scale_envelope S c delta A < +oo ->
  metric_scale_envelope S c delta (caratheodory_density_good_set S c omega A t eta)=0.
Proof.
move=> hc hclosed ho ht hde hfin.
have [ht0 ht1] := andP ht.
pose nu := metric_scale_envelope S c delta.
have hn := metric_scale_envelope_specification S c delta.
have hm := @metric_scale_envelope_measure R X J S c delta hc.
pose B := caratheodory_density_good_set S c omega A t eta.
pose D := caratheodory_density_good_set S c nu A t delta.
have hDA : D `<=` A := @caratheodory_density_good_set_subset R X J S c nu A t delta.
have hsub : B `<=` D.
  move=> x [hx hb]; split=> // j hS hd.
  rewrite (@metric_scale_intersection_agreement R X J S c delta nu omega hc hclosed hn ho j A hd).
  exact: hb j hS (le_trans hd hde).
have hq0 : 0<=nu D := @measure_nonnegative R X nu hm D.
have hqfin : nu D < +oo.
  exact: le_lt_trans (@measure_mono R X nu hm D A hDA) hfin.
have hb := @caratheodory_density_good_set_bound R X J S c nu nu A t delta hm hc ht0 hn.
have heq : nu D=0 := finite_nonnegative_self_contraction_zero hq0 hqfin ht1 hb.
apply/eqP; rewrite eq_le (@measure_nonnegative R X nu hm B) andbT.
rewrite -heq; exact (@measure_mono R X nu hm B D hsub).
Qed.

(** Source for [caratheodory_density_good_set_null]: supporting zero final
    measure of B(phi_infinity,t,eta) in 2.10.17(3), p. 179 Every
    sufficiently small approximation is zero; the abstract supremum laws
    give the asserted final value without a separate limit assumption. *)
Theorem caratheodory_density_good_set_null (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (c : J -> \bar R)
    (omega psi : set X -> \bar R) (A : set X) (t : R) (eta : \bar R) :
  (forall j, 0<=c j) -> is_intersection_cost_family S c ->
  is_metric_scale_envelope S c +oo omega -> is_caratheodory_limit S c psi ->
  (forall delta : \bar R, 0<delta -> metric_scale_envelope S c delta A < +oo) ->
  (0<t<1)%R -> 0<eta -> psi (caratheodory_density_good_set S c omega A t eta)=0.
Proof.
move=> hc hclosed ho hpsi hfinite ht heta.
pose B := caratheodory_density_good_set S c omega A t eta.
have hpos : 0<=psi B.
  have hn := metric_scale_envelope_specification S c eta.
  exact: le_trans (metric_scale_envelope_nonnegative hn B)
    (@caratheodory_limit_upper R X J S c psi hpsi B eta _ heta hn).
apply/eqP; rewrite eq_le hpos andbT.
apply: (caratheodory_limit_least hpsi)=> delta nu hd hn.
pose e := Order.min delta eta.
have he : 0<e by rewrite /e lt_min hd heta.
have hed : e<=delta by rewrite /e ge_min lexx.
have heeta : e<=eta by rewrite /e ge_min lexx orbT.
have hzero := @caratheodory_density_good_set_small_scale_zero R X J S c omega A t eta e
  hc hclosed ho ht heeta (hfinite e he).
have henv := metric_scale_envelope_specification S c e.
have hbound := @metric_scale_envelope_antitone_cutoff R X J S c e delta
  (metric_scale_envelope S c e) nu henv hn hed B.
by rewrite hzero in hbound.
Qed.
