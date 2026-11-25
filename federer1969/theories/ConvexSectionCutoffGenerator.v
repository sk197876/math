(** Finite-cutoff generator comparison for the all-set
    section inequality in Federer (1969), 3.2.45, p. 280. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex EuclideanBlockCoordinates
  EuclideanLebesgueDimensions ProjectionMeasureUP IntegralGeometricGauge CompactConvexBlockSections
  CompactConvexIntrinsicSectionComparisonAll CartesianSectionDiameter EuclideanClosedDiameterCompact
  MetricDiameter MetricScaleEnvelopeUP MetricScaleWeightedBound BorelClosedProjection TopologicalBorel SuslinSetUP
  ExtendedRealOrderTopology MeasureUP MeasureIntegralUP PartialFunctionUP PartialFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_section_cutoff_generator_majorant]: supporting
    closed-convex cover step in Federer 3.2.45,
    p. 280. A source generator at the finite
    cutoff is compact. Its original section gauges
    form a nonnegative function with a finite ordinary
    integral bounded by its original intrinsic cost.
    Each original section is itself an admissible
    closed convex cutoff generator, including empty
    and thin sections. The infimum law bounds its
    cutoff measure by that actual gauge. No source
    or target measure comparison is assumed. *)
Theorem convex_section_cutoff_generator_majorant (R : realType) m q k (hKQ : (k<=q)%N)
    (B : closed_convex_euclidean_sets R (m+q)) (d : R)
    (nu : set (inner_metric_space (@euclidean_inner_productP R q)) -> \bar R) :
  is_metric_scale_envelope
    (fun j : closed_convex_euclidean_sets R q => val j)
    (fun j => @integral_geometric_gauge R q k hKQ 1 (val j)) d%:E nu ->
  extended_metric_diameter (val B)<=d%:E ->
  let F := fun y : inner_metric_space (@euclidean_inner_productP R m) =>
    [set z | val B (@euclidean_block_join R m q (y,z))] in
  let rho := fun y : inner_metric_space (@euclidean_inner_productP R m) =>
    (@integral_geometric_gauge R q k hKQ 1 (F y) : extended_real_line R) in
  exists a : R, (forall y, 0<=rho y) /\
    is_measure_integral (@euclidean_lebesgue_measure R m) (partial_function_total rho) a%:E /\
    a%:E<= @integral_geometric_gauge R (m+q) (m+k) (leq_add (leqnn m) hKQ) 1 (val B) /\
    forall y, nu (F y)<=rho y.
Proof.
move=> hNu hDiameter F rho.
pose Y := inner_metric_space (@euclidean_inner_productP R q).
have hCompact := @euclidean_closed_finite_diameter_compact R (m+q) (val B) d (set_valP B).1 hDiameter.
have hConvex : is_inner_convex (val B) := (set_valP B).2.
have hFCompact y : @compact Y (F y) := @euclidean_block_section_compact R m q (val B) y hCompact.
have hFClosed y : @closed Y (F y) := compact_closed (@metric_hausdorff R Y) (hFCompact y).
have hFConvex y : is_inner_convex (F y) := @euclidean_block_section_inner_convex R m q (val B) y hConvex.
have hNonnegative y : 0<=rho y.
  exact: (@integral_geometric_gauge_nonnegative R q k hKQ 1 (lexx 1) (F y)
    (metric_borel_suslin (closed_borel_set (hFClosed y)))).
have [a [hIntegral hBound]] := @compact_convex_intrinsic_section_comparison_all R m q k hKQ
  (val B) hCompact hConvex.
exists a; split; first exact hNonnegative.
split; first exact hIntegral.
split; first exact hBound.
move=> y.
pose j : closed_convex_euclidean_sets R q := Sub (F y) (mem_set (conj (hFClosed y) (hFConvex y))).
have hSize : extended_metric_diameter (F y)<=d%:E.
  exact: le_trans (@euclidean_block_section_diameter_bound R m q (val B) y) hDiameter.
exact: (@metric_scale_generator_bound R Y (closed_convex_euclidean_sets R q)
  (fun j => val j) (fun j => @integral_geometric_gauge R q k hKQ 1 (val j)) d%:E nu j
  hNu (hNonnegative y) hSize).
Qed.
