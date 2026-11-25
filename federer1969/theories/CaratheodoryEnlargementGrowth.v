(** Federer's strict enlargement assumption, 2.10.18, p. 180. Interpret
    zeta(hat S) in its printed domain F, and derive the
    controlled-enlargement laws. the stricter printed condition implies
    positive finite generator costs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import MetricDiameterUP MetricDiameter DiameterEnlargements CaratheodoryEnlargementUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [strict_enlargement_positive_finite_cost]: supporting
    consequence of zeta(hat S)<eta zeta(S)<infinity
    in 2.10.18, p. 180. No assumption on the
    sign of the finite real eta is added: existence
    of an eligible S itself forces eta positive. *)
Lemma strict_enlargement_positive_finite_cost (R : realType) (a b : \bar R) (eta : R) :
  0<=a -> 0<=b -> b<eta%:E*a -> eta%:E*a < +oo ->
  (0<eta)%R /\ 0<a /\ a < +oo.
Proof.
move=> ha hb hstrict hfinite.
have hp : 0<eta%:E*a := le_lt_trans hb hstrict.
have heta : (0<eta)%R.
  rewrite ltNge; apply/negP=> hn.
  have he : eta%:E<=0 by rewrite lee_fin.
  have hh := lee_wpmul2r ha he.
  rewrite mul0e in hh.
  by have := lt_le_trans hp hh; rewrite ltxx.
split=> //; split.
- rewrite lt_def ha andbT; apply/eqP=> hz.
  by move: hp; rewrite hz mule0 ltxx.
- case: (ltP a +oo)=> // hn.
  have he : a=+oo by apply/eqP; rewrite eq_le leey hn.
  have hetaE : 0<eta%:E by rewrite lte_fin.
  by move: hfinite; rewrite he (gt0_muley hetaE) ltxx.
Qed.

(** Source for [diameter_enlargement_scaled_bound]: supporting
    uniform diameter control of hat S in 2.10.18(1),
    p. 180. The finite five-diameter estimate extends
    to unbounded S without constructing a real diameter. *)
Lemma diameter_enlargement_scaled_bound (R : realType) (X : metricType R)
    (F : set (set X)) S :
  extended_metric_diameter (diameter_enlargement F S)<=5%:E*extended_metric_diameter S.
Proof.
have hn := metric_diameter_nonnegative (extended_metric_diameter_specification S).
case he : (extended_metric_diameter S)=> [r| |] in hn *.
- rewrite -EFinM; apply: diameter_enlargement_bound; first by move: hn; rewrite lee_fin.
  by rewrite he.
- have h5 : (0<5%:E :> \bar R) by rewrite lte_fin ltr0n.
  by rewrite (gt0_muley h5) leey.
- by move: hn; rewrite leNgt ltNyr.
Qed.

(** Source for [federer_caratheodory_enlargement_laws]: supporting
    realisation of the abstract enlargement laws by
    Federer's displayed hat S, 2.10.18, p. 180.
    The domain requirement hat S in F is explicit;
    it is implicit in the printed zeta(hat S).
    The auxiliary control max(eta,5) changes no theorem statement. *)
Theorem federer_caratheodory_enlargement_laws (R : realType) (X : metricType R)
    (F : set (set X)) (c : set X -> \bar R) (eta : R) :
  (forall S, F S -> 0<=c S) ->
  (forall S, F S -> F (diameter_enlargement F S)) ->
  (forall S, F S -> c (diameter_enlargement F S)<eta%:E*c S /\ eta%:E*c S < +oo) ->
  is_caratheodory_enlargement F c (diameter_enlargement F) (Num.max eta 5)%R.
Proof.
move=> hc hF hg.
have h5 : (5<=Num.max eta 5)%R by rewrite le_max lexx orbT.
have heta : (eta<=Num.max eta 5)%R by rewrite le_max lexx.
have hcost S (hS : F S) := strict_enlargement_positive_finite_cost
  (hc S hS) (hc _ (hF S hS)) (hg S hS).1 (hg S hS).2.
constructor.
- have hp : (0<5 :> R)%R by rewrite ltr0n.
  exact: lt_le_trans hp h5.
- move=> S hS; exact: (hcost S hS).2.1.
- move=> S hS; exact: (hcost S hS).2.2.
- exact: hF.
- by move=> S hS x hx.
- move=> S hS; apply: le_trans (diameter_enlargement_scaled_bound F S) _.
  apply: lee_wpmul2r; first exact: metric_diameter_nonnegative (extended_metric_diameter_specification S).
  by rewrite lee_fin.
- move=> S hS; apply: le_trans (ltW (hg S hS).1) _.
  apply: lee_wpmul2r; first exact: hc.
  by rewrite lee_fin.
Qed.
