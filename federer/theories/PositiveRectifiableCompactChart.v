(** Federer (1969), 3.2.18, p. 255: every positive measurable
    remainder contains a positive compact chart image with the complete
    printed global, inverse and differential bounds. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanClosedBallCompact RectifiableSetUP RectifiableCompactChartsUP
  RectifiablePositiveParametrization EuclideanInjectiveImageCover PositiveCountableCoverPiece
  InjectiveDifferentialPieceUP InjectivePieceCoordinates CompactChartFromBiLipschitzPiece
  ZeroDimensionalCompactChart ProperMetricPositiveCompact LipschitzUP LipschitzFunctionCompact
  HausdorffMeasure HausdorffClosedCoverAgreement MeasureUP MeasureBasic
  MeasureFiniteClosure BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_rectifiable_compact_chart]: supporting positive
    compact-piece selection in Federer 3.2.18, p. 255. The positive
    dimension proof expands the printed combination of 3.2.14, 3.2.4,
    3.2.2, 2.10.43 and 2.2.3. Compact target selection precedes source
    preimage measurability, and the dimension-zero case uses a point. *)
Theorem positive_rectifiable_compact_chart (R : realType) m n
    (lambda : R) (W A : set (R_n R n)) :
  1<lambda ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) A ->
  A `<=` W ->
  (0<@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m A)%E ->
  exists C, @is_rectifiable_chart_piece R m n lambda W C /\ C `<=` A /\
    (0<@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m C)%E.
Proof.
move=> hLam; have hLamPos : 0<lambda := lt_trans ltr01 hLam.
case: m=> [|m] hW hAm hAW hAPos.
- have [b hb] : exists b, A b.
    apply: contrapT=> hNone; have hEmpty : A=set0.
      apply/seteqP; split=> x; [move=> hx; apply: hNone; by exists x|by move=> []].
    by rewrite hEmpty (measure_empty (@hausdorff_measure_is_measure R _ 0)) ltxx in hAPos.
  have [hChart [hImage hMass]] := @zero_dimensional_compact_chart R n lambda b (ltW hLamPos).
  exists [set b]; split.
  + split; first by move=> y ->; exact: hAW b hb.
    exists [set 0],(fun _=>b); split=> //; exact: esym hImage.
  + split; first by move=> y ->.
    by rewrite hMass lte_fin ltr01.
- pose Y := inner_metric_space (@euclidean_inner_productP R n).
  pose mu := @hausdorff_measure R Y m.+1.
  have hm := @hausdorff_measure_is_measure R Y m.+1.
  have hReg := @hausdorff_measure_borel_regular R Y m.+1.
  have [f [hLip hPos]] := rectifiable_positive_global_parametrization hW hAW hAPos.
  have [G [hG hLoss]] := euclidean_injective_piece_image_cover hLip hLam.
  have [E [hE hEPos]] := @positive_countable_cover_piece R Y
    [the choiceType of set (R_n R m.+1)] mu A (f @` setT) G
    (fun E=>f @` E) hm hG.1 hLoss hPos.
  have hPiece := hG.2.2 E hE.
  have hEB := euclidean_injective_piece_image_borel hLip hPiece.
  have hImageMeas := borel_regular_borel_measurable hm hReg hEB.
  have hInterMeas := measure_measurable_intersection hm hAm hImageMeas.
  have hInterW : A `&` (f @` E) `<=` W by move=> x hx; exact: hAW x hx.1.
  have hInterFin : (mu (A `&` (f @` E))< +oo)%E.
    exact: (le_lt_trans (measure_mono hm hInterW) hW.2).
  have hProper : metric_boundedly_compact [the metricType R of Y].
    move=> b r _; exact: euclidean_closed_metric_ball_compact.
  have [C [hC [hCSub hCPos]]] := @proper_metric_positive_compact_subset R
    [the metricType R of Y] mu (A `&` (f @` E)) 0 hm hReg hProper
    hInterMeas hInterFin hEPos.
  have hCFin : (mu C< +oo)%E := le_lt_trans (measure_mono hm hCSub) hInterFin.
  have [s [t [hST [hTS [hSB [hBi hDiff]]]]]] := injective_piece_uniform_coordinates hPiece.
  have hCS : C `<=` ((fun a=>f (t a)) @` (s @` E)).
    move=> y hy; have [x hx hxy] := (hCSub y hy).2.
    exists (s x); first by exists x.
    by rewrite hST.
  have [K [g [hChart [hGC hGPos]]]] := @compact_chart_from_bilipschitz_piece R m.+1 n
    (s @` E) (fun a=>f (t a)) lambda C hSB hBi hLamPos hDiff hC hCS hCPos hCFin.
  exists (g @` K); split.
  + split; first by move=> y hy; exact: hAW y (hCSub y (hGC y hy)).1.
    exists K,g; by split.
  + split; first by move=> y hy; exact: (hCSub y (hGC y hy)).1.
    exact hGPos.
Qed.
