(** Federer (1969), 2.10.23, p. 186, invoking the final compact inequality
    of 2.10.20, p. 182. Continuous compact costs permit the needed
    open-envelope comparison. They need not be monotone, so the printed
    stronger cost-infimum equality is not assumed here: arbitrarily cheap
    interior-containing refinements suffice. Source context:
    CompactGeneratorCostUP.v. no identical compact-cost corollary was
    located. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSetDistanceProfile CompactMetricBounded CompactGeneratorCostUP
  CompactOuterApproximation MetricDiameter MetricScaleEnvelopeUP MetricScaleCutoffCost
  MetricScaleWeightedBound MetricScaleMeasureBound MeasureUP MeasureBasic OpenCoverContentUP
  OpenCoverEnvelope CompactOpenEnvelopeBound ExtendedRealBounds ExtendedScaledErrorBound
  LipschitzFunctionCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_cost_open_envelope_comparison]: supporting
    compact refinement comparison used in 2.10.23,
    p. 186. This is the sufficient implication
    from the neighbourhood argument of 2.10.20,
    p. 182, without assuming monotone costs. *)
Theorem compact_cost_open_envelope_comparison (R : realType) (X : metricType R)
    (c : compact_metric_set X -> R) (hc : is_continuous_positive_compact_cost c)
    (xi delta : R) (small large omega : set X -> \bar R) :
  metric_boundedly_compact X -> xi<delta ->
  is_metric_scale_envelope (fun C : compact_metric_set X=>val C) (fun C=>(c C)%:E) xi%:E small ->
  is_metric_scale_envelope (fun C : compact_metric_set X=>val C) (fun C=>(c C)%:E) delta%:E large ->
  is_open_cover_envelope large omega -> is_measure omega ->
  forall A, (omega A<=small A)%E.
Proof.
move=> hX hxd hs hl ho hom.
have hc0 C : (0<=(c C)%:E)%E by rewrite lee_fin; exact: (@compact_cost_nonnegative_law R X c hc C).
have hm := metric_scale_envelope_is_measure hl hc0.
apply: (measure_bounded_by_metric_scale_envelope hs hom)=> C hC.
rewrite compact_metric_diameter_finite_value lee_fin in hC.
have hdiam : compact_metric_diameter C<delta := le_lt_trans hC hxd.
apply: (@extended_upper_bound_from_scaled_errors R (omega (val C)) (c C) 1 (@ler01 R))=> e he.
have hcost : c C<c C+e by rewrite ltrDl.
have [D [hCD [hDd hDc]]] := @compact_cost_open_refinement R X c hc C delta (c C+e) hX hdiam hcost.
have h1 := @open_cover_envelope_lower R X large omega ho (val C) (interior (val D)) (open_interior _) hCD.
have h2 := @measure_mono R X large hm (interior (val D)) (val D) (fun x hx=>interior_subset hx).
have hdc : (extended_metric_diameter (val D)<=delta%:E)%E.
  rewrite compact_metric_diameter_finite_value lee_fin; exact: ltW hDd.
have h3 := @metric_scale_generator_bound R X (compact_metric_set X) (fun C=>val C) (fun C=>(c C)%:E)
  delta%:E large D hl (hc0 D) hdc.
apply: le_trans (le_trans h1 (le_trans h2 h3)) _; rewrite mul1r lee_fin; exact: ltW hDc.
Qed.

(** Source for [compact_cost_decreasing_intersection_bound]: supporting
    final compact inequality of 2.10.20, p. 182,
    in the continuous compact-cost setting needed by
    2.10.23, p. 186. A common lower bound
    at the larger cutoff bounds the smaller-cutoff
    mass of the compact intersection, including empty
    intersections and infinite lower bounds. *)
Theorem compact_cost_decreasing_intersection_bound (R : realType) (X : metricType R)
    (c : compact_metric_set X -> R) (hc : is_continuous_positive_compact_cost c)
    (xi delta : R) (small large : set X -> \bar R) (C : nat -> set X) (b : \bar R) :
  metric_boundedly_compact X -> xi<delta ->
  is_metric_scale_envelope (fun D : compact_metric_set X=>val D) (fun D=>(c D)%:E) xi%:E small ->
  is_metric_scale_envelope (fun D : compact_metric_set X=>val D) (fun D=>(c D)%:E) delta%:E large ->
  (forall n, compact (C n)) -> (forall n m, (n<=m)%N -> C m `<=` C n) ->
  (forall n, (b<=large (C n))%E) -> (b<=small (\bigcap_n C n))%E.
Proof.
move=> hX hxd hs hl hC hdec hb.
have hc0 D : (0<=(c D)%:E)%E by rewrite lee_fin; exact: (@compact_cost_nonnegative_law R X c hc D).
have hm := metric_scale_envelope_is_measure hl hc0.
pose ha := measure_open_cover_content hm.
pose omega := @open_cover_envelope R X large ha.
have ho := @open_cover_envelope_specification R X large ha.
have hom := @open_cover_envelope_is_measure R X large ha.
have hcl n : closed (C n) := compact_closed (@metric_hausdorff R X) (hC n).
have h1 := compact_decreasing_open_envelope_bound hm ho (hC 0%N) hcl hdec.
have h2 := @compact_cost_open_envelope_comparison R X c hc xi delta small large omega hX hxd hs hl ho hom (\bigcap_n C n).
have h0 : (b<=extended_real_inf [set x | exists n, x=large (C n)])%E.
  apply: extended_real_inf_greatest=> x [n ->]; exact: hb n.
exact: le_trans h0 (le_trans h1 h2).
Qed.
