(** Federer (1969), 3.2.22(2), p. 258:
    almost every fibre is Hausdorff rectifiable with
    finite complementary mass and is Hausdorff measurable.
    All printed natural-dimension cases are included. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP
  RectifiableSetUP RectifiableCompactCharts RectifiableCompactChartsUP
  RectifiableChartCoverFibreRectifiability RectifiableCoareaBoundaryFibres RectifiableCoareaRemainders
  FiniteHausdorffFibres HausdorffMeasure MappingMultiplicity MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_coarea_fibres]: the whole
    assertion (2) in Federer 3.2.22, p. 258,
    for the auxiliary global Lipschitz extension F
    agreeing with the original map on W. Strict
    dimensions use the chart-pair fibre covers and
    both null remainders; equal dimensions use finite
    counting fibres. The general 2.10.25 bound proves
    finite mass independently of the sharp coarea formula,
    and 2.10.26 supplies actual measurability. There
    is no positive-degree, ambient-dimension, derivative-field
    or extra finite-fibre premise. *)
Theorem rectifiable_coarea_fibres (R:realType) m n mu v
    (W:set (R_n R n)) (Z:set (R_n R v))
    (F:inner_metric_space (@euclidean_inner_productP R n)->
      inner_metric_space (@euclidean_inner_productP R v)):
  (mu<=m)%N ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) mu Z ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) Z ->
  is_metric_lipschitz setT F ->(forall w,W w ->Z (F w)) ->
  measure_almost_everywhere (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) [set z|
      is_measure_m_rectifiable (@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) (m-mu)) (m-mu) (mapping_fibre F W z) /\
      measure_measurable (@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) (m-mu)) (mapping_fibre F W z)].
Proof.
move=>hDim hRectW hW hRectZ hZ hF hRange.
have [hEq|hEq]:=eqVneq mu m.
- subst mu; rewrite subnn.
  exact:(rectifiable_coarea_equal_dimension_fibres hW hRectW.2 hF).
have hStrict:(mu<m)%N by rewrite ltn_neqAle hEq hDim.
have hTwo:(1<(2:R))%R by rewrite ltr1n.
have [K [psi hSource]]:=@federer_3_2_18 R m n 2 W hRectW hW hTwo.
have [C [gamma hTarget]]:=@federer_3_2_18 R mu v 2 Z hRectZ hZ hTwo.
have hCountably:=@rectifiable_chart_cover_fibres_countably_rectifiable R m n mu v 2 W Z
  K psi C gamma F hStrict hF hSource hTarget hRange.
have hFinite:=@finite_hausdorff_fibres_almost R n v m mu F W hDim hF hRectW.2.
have hMeas:=@rectifiable_coarea_fibre_measurability R n v m mu F W hDim hF hW hRectW.2.
have hb:=@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R v)) mu.
have hBoth:=measure_almost_everywhere_and hb hCountably
  (measure_almost_everywhere_and hb hFinite hMeas.2).
apply:(measure_almost_everywhere_mono hb _ hBoth)=>z [hCz [hFz hMz]].
split; last exact hMz; by split.
Qed.
