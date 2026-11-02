(** Federer (1969), 3.2.22, pp. 258–260:
    the intrinsic Jacobian vanishes almost everywhere
    on the part omitted by the chart-pair union. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionExtensionUP
  MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic HausdorffMeasure MeasureApproximateJacobian
  RectifiableSetUP RectifiableCompactChartsUP RectifiableChartPairPieces RectifiableChartPairFamily
  RectifiableNullTargetJacobian.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_chart_pair_omitted_jacobian_zero]:
    the first countable-sum identity in Federer 3.2.22,
    p. 259. Null-target rank gives zero intrinsic
    Jacobian on the target remainder; the source remainder
    is H^m-null. Keep both remainders as required
    by erratum p. 5, book p. 258 lines 20/22.
    The compact charts may cover any measurable subset A
    of W while the approximate Jacobian remains that of
    the original W, as needed on p. 260. *)
Theorem rectifiable_chart_pair_omitted_jacobian_zero (R:realType) m n mu v
    (lambda:R) (W A:set (R_n R n)) (Z:set (R_n R v))
    (K:nat->set (R_n R m)) (psi:nat->R_n R m->R_n R n)
    (C:nat->set (R_n R mu)) (gamma:nat->R_n R mu->R_n R v)
    (F:inner_metric_space (@euclidean_inner_productP R n)->
      inner_metric_space (@euclidean_inner_productP R v)) (J0:R_n R n->R):
  A `<=` W ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  is_metric_lipschitz setT F ->(forall w,W w ->Z (F w)) ->
  is_rectifiable_compact_chart_cover lambda A K psi ->
  is_rectifiable_compact_chart_cover lambda Z C gamma ->
  is_partial_function_total_extension
    (measure_approximate_jacobian (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) W) m mu
      (partial_function_source_restrict W (partial_function_total F))) J0 ->
  measure_almost_everywhere_on (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m)
    (A `\` (\bigcup_(p in @setT (nat*nat))
      rectifiable_chart_pair_piece (K p.1) (C p.2) (psi p.1) F (gamma p.2))) [set w|J0 w=0%R].
Proof.
move=>hAW hRectW hW hF hRange hSource hTarget hJ0.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose rho:=@hausdorff_measure R X m.
have hr:=@hausdorff_measure_is_measure R X m.
pose SrcR:=A `\` (\bigcup_i psi i @` K i).
pose TarQ:=Z `\` (\bigcup_j gamma j @` C j).
have hZero:=@rectifiable_null_target_jacobian_zero R m n v mu W F TarQ J0
  hRectW hW hF hTarget.2.2 hJ0.
have hNotR:measure_almost_everywhere rho (~`SrcR).
  rewrite /measure_almost_everywhere setCK; exact hSource.2.2.
have hBoth:=measure_almost_everywhere_and hr
  ((measure_almost_everywhere_on_implication _ _ _).1 hZero) hNotR.
have hRangeA w:A w ->Z (F w) by move=>hw; exact:(hRange w (hAW w hw)).
have hDecomposition:=rectifiable_chart_pair_remainder_cover hSource hTarget hRangeA.
apply:(measure_almost_everywhere_on_implication _ _ _).2.
apply:(measure_almost_everywhere_mono hr _ hBoth)=>w [hZeroW hOutside] [ha hNot].
have hCoverA:=ha; rewrite hDecomposition in hCoverA.
have [[[ha0 hQ]|[p _ hp]]|hR]:=hCoverA.
- exact:(hZeroW (conj (hAW w ha) hQ)).
- exfalso; apply:hNot; by exists p.
- by exfalso; exact:(hOutside hR).
Qed.
