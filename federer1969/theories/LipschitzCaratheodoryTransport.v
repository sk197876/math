(** Supporting cover comparison for Federer (1969), 2.10.11, p. 176:
    transport generators through a map which multiplies diameters by at most
    L and costs by at most a. At a target cutoff choose a smaller source
    cutoff, then apply the weighted envelope bound. This generalises the
    existing nonexpanding transport without exposing a construction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureIndexedCover MetricDiameter
  MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleCutoffCost MetricScaleWeightedBound
  CaratheodoryLimitUP CaratheodoryBorelRegular.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lipschitz_caratheodory_transport]: supporting
    diameter/cost-scaled covering comparison for Federer
    2.10.11, p. 176. Positive constants L and a permit
    the cutoff change and reciprocal cost scaling. Degenerate
    zero constants are handled separately in applications. *)
Theorem lipschitz_caratheodory_transport (R : realType) (X Y : metricType R)
    (J K : choiceType) (S : J -> set X) (T : K -> set Y)
    (c : J -> \bar R) (d : K -> \bar R) (f : X -> Y) (v : J -> K)
    (mu : set X -> \bar R) (xi : set Y -> \bar R) (L a : R) :
  is_caratheodory_limit S c mu -> is_caratheodory_limit T d xi ->
  (forall k, 0<=d k) -> (0<L)%R -> (0<a)%R ->
  (forall j x, S j x -> T (v j) (f x)) ->
  (forall j, extended_metric_diameter (T (v j))<=L%:E*extended_metric_diameter (S j)) ->
  (forall j, d (v j)<=a%:E*c j) -> forall A, xi (f @` A)<=a%:E*mu A.
Proof.
move=> hm hx hd hL ha hmap hdiam hcost A.
apply: (caratheodory_limit_least hx)=> delta tau hdelta htau.
have [k hk] := reciprocal_metric_cutoffs_cofinal hdelta.
pose r : R := (((k.+1)%:R)^-1)%R.
have hr : (0<r)%R by rewrite /r invr_gt0 ltr0n.
pose e : R := (r/L)%R.
have he : (0<e)%R by rewrite /e divr_gt0.
pose nu := metric_scale_envelope S c e%:E.
have hnu := metric_scale_envelope_specification S c e%:E.
have htmeasure := metric_scale_envelope_is_measure htau hd.
pose q (B : set X) := tau (f @` B).
have hq : is_measure q.
  constructor; first by move=> B; exact: measure_nonnegative htmeasure _.
  move=> B G hG hcov.
  apply: (@measure_indexed_cover R Y [the choiceType of set X] tau htmeasure
    (f @` B) G (fun C => f @` C) hG).
  move=> y [x hxB <-]; have [C hC hxC] := hcov x hxB; exists C=> //; by exists x.
have hgen j : extended_metric_diameter (S j)<=e%:E -> q (S j)<=a%:E*c j.
  move=> hsize.
  have hsize' : extended_metric_diameter (T (v j))<=delta.
    apply: le_trans (hdiam j) _.
    have hh := lee_wpmul2l (ltW (hL : 0<L%:E)) hsize.
    have hLe : (L*e)%R=r by rewrite /e mulrC divfK ?gt_eqF.
    rewrite -EFinM hLe in hh; exact: le_trans hh hk.
  have hsub : f @` S j `<=` T (v j).
    move=> y [x hxs <-]; exact: hmap j x hxs.
  apply: le_trans (@measure_mono R Y tau htmeasure _ _ hsub) _.
  exact: le_trans (@metric_scale_generator_bound R Y K T d delta tau (v j) htau (hd (v j)) hsize') (hcost j).
have hb := @measure_bounded_by_scaled_metric_envelope R X J S c e%:E nu q a hnu hq ha hgen A.
apply: le_trans hb _; apply: lee_wpmul2l; first exact: ltW (ha : 0<a%:E).
exact: (@caratheodory_limit_upper R X J S c mu hm A e%:E nu he hnu).
Qed.
