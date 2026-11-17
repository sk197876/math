(** Expanded continuity support for Federer (1969), 3.2.45,
    p. 279: the original projection-volume supremum of a compact
    convex body is attained in the original projection space. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  EuclideanProjectionSpace EuclideanProjectionMetric ProjectedVolumeMeasurability ProjectedVolumeGauge
  CompactConvexProjectedGaugeFinite CompactConvexProjectionRelativeError RealMetricBackground
  NormMetricScaleContinuity CompactMaximum EuclideanLebesgueDimensions MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_convex_projection_maximum]: expanded
    support for the exponent infinity endpoint in Federer 3.2.45,
    p. 279. The proved relative error makes the finite scalar
    profile continuous on the original compact projection space;
    the original supremum laws then identify its attained maximum.
    Empty bodies, zero projection volume and degree zero remain. *)
Theorem compact_convex_projection_maximum (R : realType) n m (hMN : (m <= n)%N)
    (K : set (inner_metric_space (@euclidean_inner_productP R n))) :
  compact K -> is_inner_convex K ->
  exists p : orthogonal_projection_metric_space R n m,
    projected_volume_function K p = @projected_volume_gauge R n m K.
Proof.
move=> hCompact hConvex.
pose P := orthogonal_projection_metric_space R n m.
pose C := @projected_volume_gauge R n m K.
pose c : R := fine C.
pose f (p : P) : real_line_metric R := fine (projected_volume_function K p).
have hCValue : C = c%:E := @compact_convex_projected_gauge_finite_value R n m hMN K hCompact hConvex.
have hCFinite : C < +oo := @compact_convex_projected_gauge_finite R n m hMN K hCompact hConvex.
have hc : (0 <= c)%R.
  have h := @projected_volume_gauge_nonnegative R n m K hMN.
  by rewrite -/C hCValue lee_fin in h.
have hContinuous : continuous f.
  apply: (@metric_fixed_lipschitz_continuous R P [the metricType R of real_line_metric R]
    f (m%:R*c)%R (mulr_ge0 (ler0n R m) hc))=> p q.
  rewrite real_line_metric_distanceE.
  have h := @compact_convex_projection_relative_error R n m hMN K hCompact hConvex p q.
  change (is_true (`|f p-f q| <= m%:R*mdist p q*c)%R) in h.
  by rewrite mulrAC in h.
have hNE : [set: P] !=set0.
  have [q hQ] := @euclidean_projection_exists R n m hMN.
  have [p _] := @euclidean_projection_linear_complete R n m q hQ.
  by exists p.
have [p [_ hMax]] := continuous_compact_maximum hNE (@euclidean_projection_space_compact R n m) hContinuous.
have hValue (r : P) : projected_volume_function K r = (f r)%:E.
  symmetry; apply: fineK.
  rewrite (ge0_fin_numE (measure_nonnegative (euclidean_lebesgue_is_measure R m) _)).
  apply: le_lt_trans _ hCFinite.
  exact: (@projected_volume_gauge_projection_bound R n m K (euclidean_projection_linear r)
    (euclidean_projection_linear_member r)).
have hSup : C <= (f p)%:E.
  apply: projected_volume_gauge_least_bound=> q hQ.
  have [r hR] := @euclidean_projection_linear_complete R n m q hQ.
  have hImage : q @` K = euclidean_projection_linear r @` K.
    symmetry; apply: eq_imagel=> x _; exact: hR.
  rewrite hImage -/(projected_volume_function K r) hValue.
  exact: lee_tofin (hMax r I).
exists p; apply/eqP; rewrite eq_le; apply/andP; split.
- exact: (@projected_volume_gauge_projection_bound R n m K (euclidean_projection_linear p)
    (euclidean_projection_linear_member p)).
- by rewrite hValue; exact hSup.
Qed.
