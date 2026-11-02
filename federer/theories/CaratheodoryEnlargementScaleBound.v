(** Scale comparison in Federer (1969), 2.10.18(1), p. 180, proof. Retain a
    finite selected head, let the enlarged tail mass tend to zero, then take
    the supremum over cutoffs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MetricDiameterUP MetricDiameter
  MetricScaleEnvelopeUP MetricScaleWeightedBound MetricScaleCutoffCost
  CaratheodoryEnlargementUP CaratheodoryDensityLargeCells CaratheodoryEnlargementSelection
  FiniteRemainderMeasureComparison DiameterEnlargements CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_enlargement_scale_bound]: supporting sharp
    estimate phi_delta(B)<=mu(V)/t in 2.10.18(1), p. 180 The finite tail is
    removed at each fixed cutoff, before taking the Caratheodory supremum. *)
Theorem caratheodory_enlargement_scale_bound (R : realType) (X : metricType R)
    (F : set (set X)) (c mu : set X -> \bar R) (E : set X -> set X)
    (k : R) (B V : set X) (delta : \bar R) (nu : set X -> \bar R) (t D : R) :
  is_caratheodory_enlargement F c E k -> is_measure mu -> mu V < +oo -> (0<t)%R ->
  is_metric_scale_envelope (fun j : set_type F => val j) (fun j => c (val j)) delta nu ->
  (forall S, F S -> closed S) -> (forall S, F S -> measure_measurable mu S) ->
  (forall S, caratheodory_large_cell_family F c mu E V delta t S -> extended_metric_diameter S<=D%:E) ->
  family_covers_finely (caratheodory_large_cell_family F c mu E V delta t) B ->
  nu B<=(t^-1)%R%:E*mu V.
Proof.
move=> hE hm hV ht hnu hclosed hmeas hD hf.
pose P := caratheodory_large_cell_family F c mu E V delta t.
have hPF : P `<=` F by move=> S [hS _].
have hPC S (hS : P S) : closed S := hclosed S (hPF S hS).
have htE : 0<t%:E by rewrite lte_fin.
have htinv : (0<t^-1)%R by rewrite invr_gt0.
have hk := caratheodory_enlargement_constant_positive hE.
have hmass S (hS : P S) : 0<mu S.
  have hp := @caratheodory_enlargement_cost_positive R X F c E k hE S (hPF S hS).
  have hh : 0<t%:E*c S := mule_gt0 htE hp.
  exact: lt_trans hh hS.2.1.
have hne S (hS : P S) : S<>set0.
  move=> he; have hp := hmass S hS.
  by rewrite he (measure_empty hm) ltxx in hp.
have [G [hGP [hdis hrem]]] := @caratheodory_enlargement_selection_exists R X F P c E k D B
  hE hPF hPC hne hD hf.
have hcost (j : set_type F) : 0<=c (val j : set X).
  exact: ltW (@caratheodory_enlargement_cost_positive R X F c E k hE _ (set_valP j)).
have hn := metric_scale_envelope_is_measure hnu hcost.
have hwithin S (hS : G S) : S `<=` V.
  have hp := hGP S hS.
  move=> x hx; apply: hp.2.2.1.
  exact: (@caratheodory_enlargement_contains R X F c E k hE S hp.1 x
    (@diameter_enlargement_contains R X F S hp.1 x hx)).
have hgen S (hS : G S) : c S<=(t^-1)%R%:E*mu S.
  have hp := ltW (hGP S hS).2.1.
  have hi : 0<=(t^-1)%R%:E by rewrite lee_fin; exact: ltW htinv.
  have hh := lee_wpmul2l hi hp.
  by rewrite muleA -EFinM mulVf ?gt_eqF // mul1e in hh.
have hhead S (hS : G S) : nu S<=(t^-1)%R%:E*mu S.
  have hp := hGP S hS.
  pose j : set_type F := @exist _ (fun S : set X => S \in F) S (mem_set hp.1).
  have hdS := extended_metric_diameter_mono
    (fun x hx => @caratheodory_enlargement_contains R X F c E k hE S hp.1 x
      (@diameter_enlargement_contains R X F S hp.1 x hx)).
  have hbound : nu S<=c S := @metric_scale_generator_bound R X [the choiceType of set_type F]
    (fun j => val j) (fun j => c (val j)) delta nu j hnu (hcost j)
    (le_trans hdS (ltW hp.2.2.2)).
  exact: le_trans hbound (hgen S hS).
have htail S (hS : G S) : nu (E S)<=(k/t)%R%:E*mu S.
  have hp := hGP S hS.
  have hFS := @caratheodory_enlargement_member R X F c E k hE S hp.1.
  pose j : set_type F := @exist _ (fun S : set X => S \in F) (E S) (mem_set hFS).
  have hbound : nu (E S)<=c (E S) := @metric_scale_generator_bound R X [the choiceType of set_type F]
    (fun j => val j) (fun j => c (val j)) delta nu j hnu (hcost j) (ltW hp.2.2.2).
  apply: le_trans hbound _.
  apply: le_trans (@caratheodory_enlargement_cost R X F c E k hE S hp.1) _.
  have hkE : 0<=k%:E by rewrite lee_fin; exact: ltW hk.
  have hh := lee_wpmul2l hkE (hgen S hS).
  by rewrite muleA -EFinM in hh.
apply: (@finite_remainder_measure_comparison R X mu nu B V G E (t^-1)%R (k/t)%R
  hm hn hV hdis _ hwithin _ (ltW htinv) _ hrem hhead htail).
- move=> S hS; exact: hmeas S (hPF S (hGP S hS)).
- move=> S hS; exact: hmass S (hGP S hS).
- exact: mulr_ge0 (ltW hk) (ltW htinv).
Qed.
