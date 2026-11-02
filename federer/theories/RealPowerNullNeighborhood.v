(** Federer (1969), 2.10.47(3), p. 205: null coordinate levels admit open
    neighbourhoods of arbitrarily small fixed-cutoff cost. This follows from
    the open-envelope comparison in 2.10.20, p. 182, verified for the real
    power gauge. It is not outer regularity of Hausdorff measure by open
    sets. Source context: RealPowerCompactCost.v *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology lra.
From Federer Require Import MetricDiameter CompactOpenEnvelopeBound HausdorffLengthUP MetricRealPowerCost MetricRealPowerMeasureUP
  RealPowerCompactCost RealPowerCompactCutoff CompactCostOpenEnvelope LipschitzFunctionCompact
  MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleCutoffCost CaratheodoryLimitUP
  OpenCoverContentUP OpenCoverEnvelope OpenCoverEnvelopeApproximation MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_power_null_set_cutoff_neighbourhood]:
    supporting cheap open neighbourhood in 2.10.47(3),
    p. 205. The fixed cutoff, coefficient and real
    degree are positive. The null set itself need not
    be compact or measurable. *)
Theorem real_power_null_set_cutoff_neighbourhood (R : realType) (X : metricType R)
    (c p d e : R) (mu nu : set X -> \bar R) (A : set X) :
  metric_boundedly_compact X -> (0<c)%R -> (0<p)%R -> (0<d)%R -> (0<e)%R ->
  is_metric_real_power_measure c p mu ->
  is_metric_scale_envelope (fun S : @nonempty_metric_sets R X=>val S)
    (fun S=>metric_real_diameter_cost c p (val S)) d%:E nu ->
  mu A=0 -> exists U, [/\ open U, A `<=` U & nu U<e%:E].
Proof.
move=> hX hc hp hd he hmu hn hz.
pose small := metric_scale_envelope (fun S : @nonempty_metric_sets R X=>val S)
  (fun S=>metric_real_diameter_cost c p (val S)) (d/2)%R%:E.
have hs := metric_scale_envelope_specification (fun S : @nonempty_metric_sets R X=>val S)
  (fun S=>metric_real_diameter_cost c p (val S)) (d/2)%R%:E.
have hhalf : (0<d/2)%R by lra.
have hgap : (d/2<d)%R by lra.
have hcc := @real_power_compact_generator_cost_laws R X c p hc hp.
have hsc := @real_power_compact_cutoff_laws R X c p (d/2)%R small hX (ltW hc) (ltW hhalf) hs.
have hnc := @real_power_compact_cutoff_laws R X c p d nu hX (ltW hc) (ltW hd) hn.
have hnm := metric_scale_envelope_is_measure hn
  (fun S=>@metric_real_power_cost_nonnegative R c p (extended_metric_diameter (val S)) (ltW hc)).
pose ha := measure_open_cover_content hnm.
pose omega := @open_cover_envelope R X nu ha.
have ho := @open_cover_envelope_specification R X nu ha.
have hom := @open_cover_envelope_is_measure R X nu ha.
have h1 := @compact_cost_open_envelope_comparison R X _ hcc (d/2)%R d small nu omega
  hX hgap hsc hnc ho hom A.
have h2 := @caratheodory_limit_upper R X _ _ _ mu hmu A (d/2)%R%:E small hhalf hs.
have hlt : omega A<e%:E.
  apply: le_lt_trans (le_trans h1 h2) _; by rewrite hz lte_fin.
have [U [hU [hAU hcost]]] := open_cover_envelope_strict_approximation ho hlt.
by exists U; split.
Qed.
