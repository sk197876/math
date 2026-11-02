(** Supporting containing-generator proof for Federer (1969),
    2.10.19(3)–(5), p. 181. This is an additional supporting theorem, not a
    silent change to the numbered 2.10.18 statements. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MetricDiameterUP MetricDiameter
  MetricScaleEnvelopeUP MetricScaleEnvelopeLaws MetricScaleEnvelope CaratheodoryLimitUP
  CaratheodoryBorelRegular CaratheodoryDensityLargeCells WeakCaratheodoryDensityLargeCells CaratheodoryWeakEnlargementUP
  CaratheodoryEnlargementGrowth WeakCaratheodoryEnlargementScaleBound DiameterEnlargements
  CaratheodoryDensityUpperBound MeasureDerivates CoveringFamilyUP CoveringRelationUP CoveringRelationLimits.
From Federer Require Import WeakCaratheodoryDensityQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weak_caratheodory_enlargement_density_bound]: supporting
    weak-cost enlargement argument for 2.10.19(3)–(5), p. 181 Zero costs and
    the corrected covering quotient are explicit; the printed strict 2.10.18
    is unchanged. *)
Theorem weak_caratheodory_enlargement_density_bound (R : realType) (X : metricType R)
    (F : set (set X)) (c mu psi : set X -> \bar R)
    (E : set X -> set X) (k : R) (B V : set X) (t : R) :
  is_weak_caratheodory_enlargement F c E k -> is_measure mu ->
  is_caratheodory_limit (fun j : set_type F => val j) (fun j => c (val j)) psi ->
  (forall S, F S -> closed S) -> (forall S, F S -> measure_measurable mu S) ->
  open V -> B `<=` V -> (0<t)%R ->
  (forall x, B x -> t%:E<covering_upper_limit (caratheodory_family_relation F)
    (caratheodory_measure_cost_ratio mu c) x) -> t%:E*psi B<=mu V.
Proof.
move=> hE hm hpsi hclosed hmeas ho hBV ht hlim.
case: (ltP (mu V) +oo)=> [hV|hn].
- have hcost (j : set_type F) : 0<=c (val j : set X).
    exact: (@weak_enlargement_cost_nonnegative R X F c E k hE _ (set_valP j)).
  have hbound : psi B<=(t^-1)%R%:E*mu V.
    apply: (caratheodory_limit_least hpsi)=> delta nu hd hnu.
    have [n hn] := reciprocal_metric_cutoffs_cofinal hd.
    pose d : R := ((n.+1%:R)^-1)%R.
    have hd0 : 0<d%:E := @reciprocal_metric_cutoff_positive R n.
    pose xi := metric_scale_envelope (fun j : set_type F => val j) (fun j => c (val j)) d%:E.
    have hxi := @metric_scale_envelope_specification R X [the choiceType of set_type F]
      (fun j => val j) (fun j => c (val j)) d%:E.
    have hf := @weak_caratheodory_large_cells_fine R X F c mu E k B V d%:E t hm ht hE ho hBV hd0 hlim.
    have hD S (hS : caratheodory_large_cell_family F c mu E V d%:E t S) :
        extended_metric_diameter S<=d%:E.
      apply: le_trans _ (ltW hS.2.2.2); apply: extended_metric_diameter_mono=> x hx.
      exact: (@weak_enlargement_contains R X F c E k hE S hS.1 x
        (@diameter_enlargement_contains R X F S hS.1 x hx)).
    have hb := @weak_caratheodory_enlargement_scale_bound R X F c mu E k B V d%:E xi t d
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
