(** Federer (1969), 2.10.18(1), p. 180: an open set containing points of
    upper density greater than t has measure at least t times their
    Caratheodory measure. We retain Federer's strict threshold and original
    partial quotient. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MetricDiameterUP MetricDiameter
  MetricScaleEnvelopeUP MetricScaleEnvelopeLaws MetricScaleEnvelope CaratheodoryLimitUP
  CaratheodoryBorelRegular CaratheodoryDensityLargeCells CaratheodoryEnlargementUP
  CaratheodoryEnlargementGrowth CaratheodoryEnlargementScaleBound DiameterEnlargements
  CaratheodoryDensityUpperBound MeasureDerivates CoveringFamilyUP CoveringRelationUP CoveringRelationLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_enlargement_density_bound]: supporting form of
    2.10.18(1), p. 180, allowing a controlled containing generator. Fineness
    outside B is unnecessary for this implication. *)
Theorem caratheodory_enlargement_density_bound (R : realType) (X : metricType R)
    (F : set (set X)) (c mu psi : set X -> \bar R)
    (E : set X -> set X) (k : R) (B V : set X) (t : R) :
  is_caratheodory_enlargement F c E k -> is_measure mu ->
  is_caratheodory_limit (fun j : set_type F => val j) (fun j => c (val j)) psi ->
  (forall S, F S -> closed S) -> (forall S, F S -> measure_measurable mu S) ->
  open V -> B `<=` V -> (0<t)%R ->
  (forall x, B x -> t%:E<covering_upper_limit (caratheodory_family_relation F)
    (measure_ratio_function mu c) x) -> t%:E*psi B<=mu V.
Proof.
move=> hE hm hpsi hclosed hmeas ho hBV ht hlim.
case: (ltP (mu V) +oo)=> [hV|hn].
- have hcost (j : set_type F) : 0<=c (val j : set X).
    exact: ltW (@caratheodory_enlargement_cost_positive R X F c E k hE _ (set_valP j)).
  have hbound : psi B<=(t^-1)%R%:E*mu V.
    apply: (caratheodory_limit_least hpsi)=> delta nu hd hnu.
    have [n hn] := reciprocal_metric_cutoffs_cofinal hd.
    pose d : R := ((n.+1%:R)^-1)%R.
    have hd0 : 0<d%:E := @reciprocal_metric_cutoff_positive R n.
    pose xi := metric_scale_envelope (fun j : set_type F => val j) (fun j => c (val j)) d%:E.
    have hxi := @metric_scale_envelope_specification R X [the choiceType of set_type F]
      (fun j => val j) (fun j => c (val j)) d%:E.
    have hf := @caratheodory_large_cells_fine R X F c mu E k B V d%:E t hE ho hBV hd0 hlim.
    have hD S (hS : caratheodory_large_cell_family F c mu E V d%:E t S) :
        extended_metric_diameter S<=d%:E.
      apply: le_trans _ (ltW hS.2.2.2); apply: extended_metric_diameter_mono=> x hx.
      exact: (@caratheodory_enlargement_contains R X F c E k hE S hS.1 x
        (@diameter_enlargement_contains R X F S hS.1 x hx)).
    have hb := @caratheodory_enlargement_scale_bound R X F c mu E k B V d%:E xi t d
      hE hm hV ht hxi hclosed hmeas hD hf.
    apply: le_trans _ hb.
    exact: (@metric_scale_envelope_antitone_cutoff R X [the choiceType of set_type F]
      (fun j => val j) (fun j => c (val j)) d%:E delta xi nu hxi hnu hn B).
  have ht0 : 0<=t%:E by rewrite lee_fin; exact: ltW ht.
  have hh := lee_wpmul2l ht0 hbound.
  by rewrite muleA -EFinM mulfV ?gt_eqF // mul1e in hh.
- have he : mu V=+oo by apply/eqP; rewrite eq_le leey hn.
  by rewrite he leey.
Qed.

(** Source for [federer_2_10_18_1]: direct formalisation of
    2.10.18(1), p. 180, with the printed strict
    enlargement bound and strict density threshold.
    The domain of zeta explicitly includes hat S;
    the original partial quotient is retained. *)
Theorem federer_2_10_18_1 (R : realType) (X : metricType R)
    (F : set (set X)) (c mu psi : set X -> \bar R)
    (eta : R) (B V : set X) (t : R) :
  is_measure mu -> (forall S, F S -> 0<=c S) ->
  (forall x, covering_relation_fine_at (caratheodory_family_relation F) x) ->
  is_caratheodory_limit (fun j : set_type F => val j) (fun j => c (val j)) psi ->
  (forall S, F S -> closed S) -> (forall S, F S -> measure_measurable mu S) ->
  (forall S, F S -> F (diameter_enlargement F S)) ->
  (forall S, F S -> c (diameter_enlargement F S)<eta%:E*c S /\ eta%:E*c S < +oo) ->
  open V -> B `<=` V -> (0<t)%R ->
  (forall x, B x -> t%:E<covering_upper_limit (caratheodory_family_relation F)
    (measure_ratio_function mu c) x) -> t%:E*psi B<=mu V.
Proof.
move=> hm hc hf hpsi hclosed hmeas hF hg ho hBV ht hlim.
have hE := federer_caratheodory_enlargement_laws hc hF hg.
exact: caratheodory_enlargement_density_bound hE hm hpsi hclosed hmeas ho hBV ht hlim.
Qed.
