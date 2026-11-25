(** Federer (1969), 3.2.41, printed p. 278, compact
    approximation: the actual open-tube volumes of any compact
    Euclidean set tend to its actual volume. Open outer
    approximation and a uniform compact neighbourhood supply
    the limit over every positive real radius. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanCompactOpenVolume MetricCompactNeighbourhood MetricOpenThickening
  PositiveRadiusLimits PositiveRadiusLimitBounds PositiveRadiusLowerApproximation
  ExtendedRealOrderTopology MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_ambient_tube_volume_limits]: supporting
    full positive-real-radius compact approximation in Federer
    3.2.41, p. 278. Near-optimal open supersets of the original
    compact source contain a uniform positive-radius tube.
    Monotonicity and the independent order-limit laws prove
    both limits. Empty sources and every natural ambient
    dimension are retained. No convexity, boundary regularity,
    Brunn--Minkowski inequality or selected distance is assumed. *)
Theorem compact_ambient_tube_volume_limits (R:realType) n
    (C:set (inner_metric_space (@euclidean_inner_productP R n))):
  compact C ->
  positive_radius_upper_limit (fun r:R=>@euclidean_lebesgue_measure R n
    (metric_open_thickening C r))=@euclidean_lebesgue_measure R n C /\
  positive_radius_lower_limit (fun r:R=>@euclidean_lebesgue_measure R n
    (metric_open_thickening C r))=@euclidean_lebesgue_measure R n C.
Proof.
move=> hC.
pose E:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R n.
pose f:=fun r:R=>mu (metric_open_thickening C r).
have hm:=euclidean_lebesgue_is_measure R n.
have hLower:(mu C<=positive_radius_lower_limit f)%E.
  apply:(@positive_radius_lower_eventual_bound R f (mu C) 1 ltr01)=>r /andP[hr _].
  change (is_true (mu C<=mu (metric_open_thickening C r))%E).
  exact:(@measure_mono R E mu hm _ _ (@metric_open_thickening_includes R E C r hr)).
have hUpper:(positive_radius_upper_limit f<=mu C)%E.
  rewrite leNgt; apply/negP=> hBad.
  have [q [hCQ hQU]]:=@extended_rationals_order_dense R (mu C)
    (positive_radius_upper_limit f) hBad.
  have [U [hU [hCU hVolume]]]:=@euclidean_compact_open_volume_bound R n C
    (ratr q) hC hCQ.
  have [d [hd hTube]]:=compact_metric_open_thickening hC hU hCU.
  have hBound:(positive_radius_upper_limit f<=(ratr q)%:E)%E.
    apply:(@positive_radius_upper_eventual_bound R f (ratr q)%:E d hd)=>r /andP[hr hrd].
    apply:le_trans _ (ltW hVolume).
    apply:(@measure_mono R E mu hm)=>x [c hc hcx].
    apply:hTube; exists c=>//.
    exact:(lt_trans hcx hrd).
  have hImpossible:=lt_le_trans hQU hBound.
  by rewrite ltxx in hImpossible.
have hOrder:=@positive_radius_limits_ordered R f.
split; apply/eqP; rewrite eq_le; apply/andP.
- split; [exact hUpper|exact:(le_trans hLower hOrder)].
- split; [exact:(le_trans hOrder hUpper)|exact hLower].
Qed.
