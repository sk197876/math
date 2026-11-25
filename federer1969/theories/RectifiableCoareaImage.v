(** Federer (1969), 3.2.22(1), pp. 258–259:
    the global exact tangent-image alternative, with both
    erratum-corrected source and target remainders. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP LipschitzBasic
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionExtensionUP PartialFunctionExtensionSealed
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureRestriction HausdorffMeasure
  MeasureApproximateJacobianUP MeasureApproximateJacobian
  RectifiableSetUP RectifiableCompactChartsUP RectifiableCompactCharts RectifiableChartInverseExtension
  RectifiableChartPairPieces RectifiableChartPairFamily RectifiableChartPairImageAlmost
  RectifiableApproximateJacobianValues RectifiableNullTargetJacobian RectifiableCoareaImageUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_coarea_image_almost]: assertion
    (1) of Federer 3.2.22, p. 258, for
    the globally extended auxiliary map in its proof.
    Countably many chart-pair alternatives give the exact
    target tangent image outside the target-null remainder.
    Above that remainder the actual intrinsic Jacobian
    is zero. Restore the H^m-null source remainder
    prescribed by erratum p. 5, book p. 258
    lines 20/22. No derivative field or rank premise
    is added; all natural dimensions are retained. *)
Theorem rectifiable_coarea_image_almost (R:realType) m n mu v
    (W:set (R_n R n)) (Z:set (R_n R v))
    (F:inner_metric_space (@euclidean_inner_productP R n)->
      inner_metric_space (@euclidean_inner_productP R v)):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) mu Z ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) Z ->
  is_metric_lipschitz setT F ->(forall w,W w ->Z (F w)) ->
  measure_almost_everywhere_on (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W
    (is_rectifiable_coarea_image_point m mu W Z F).
Proof.
move=>hRectW hW hRectZ hZ hF hRange.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose rho:=@hausdorff_measure R X m.
have hr:=@hausdorff_measure_is_measure R X m.
have hTwo:1<(2:R) by rewrite ltr1n.
have [K [psi hSource]]:=@federer_3_2_18 R m n 2 W hRectW hW hTwo.
have [C [gamma hTarget]]:=@federer_3_2_18 R mu v 2 Z hRectZ hZ hTwo.
pose SrcR:=W `\` (\bigcup_i psi i @` K i).
pose TarQ:=Z `\` (\bigcup_j gamma j @` C j).
pose P:=fun p:nat*nat=>rectifiable_chart_pair_piece (K p.1) (C p.2) (psi p.1) F (gamma p.2).
pose Good:=is_rectifiable_coarea_image_point m mu W Z F.
have hEach (p:nat*nat):measure_almost_everywhere rho [set w|P p w ->Good w].
  have [G [hG hInverse]]:=uniform_compact_chart_inverse_global_extension (hTarget.1 p.2).1.
  have hPair:=@rectifiable_chart_pair_image_almost R m n mu v 2 W Z (K p.1) (C p.2)
    (psi p.1) F (gamma p.2) G hTwo (hSource.1 p.1).1 (hTarget.1 p.2).1
    (hSource.1 p.1).2 (hTarget.1 p.2).2 hW hRectW.2 hZ hRectZ.2 hF
    (metric_lipschitz_of_bound hG) hInverse.
  exact:((measure_almost_everywhere_on_implication _ _ _).1 hPair.2).
pose Index:=(nat*nat)%type.
have hCount:countable (@setT (nat*nat)) by exact:countableP.
have hPairs:=@measure_almost_everywhere_countable R [the choiceType of X]
  [the choiceType of (Index:Type)] rho hr setT
  (fun p=>[set w|P p w ->Good w]) hCount (fun p _=>hEach p).
pose apJ:=measure_approximate_jacobian (measure_restrict rho W) m mu
  (partial_function_source_restrict W (partial_function_total F)).
pose J0:=@PartialFunctionExtension.value (R_n R n) R apJ 0.
have hJ0:is_partial_function_total_extension apJ J0:=@PartialFunctionExtension.laws (R_n R n) R apJ 0.
have hZero:=@rectifiable_null_target_jacobian_zero R m n v mu W F TarQ J0
  hRectW hW hF hTarget.2.2 hJ0.
have hValues:=@rectifiable_approximate_jacobian_values_almost R m n v mu W F hRectW hW hF.
have hNotR:measure_almost_everywhere rho (~`SrcR).
  rewrite /measure_almost_everywhere setCK; exact hSource.2.2.
have hAll:=measure_almost_everywhere_and hr hPairs
  (measure_almost_everywhere_and hr
    ((measure_almost_everywhere_on_implication _ _ _).1 hZero)
    (measure_almost_everywhere_and hr
      ((measure_almost_everywhere_on_implication _ _ _).1 hValues) hNotR)).
have hDecomposition:=rectifiable_chart_pair_remainder_cover hSource hTarget hRange.
apply:(measure_almost_everywhere_on_implication _ _ _).2.
apply:(measure_almost_everywhere_mono hr _ hAll)=>w [hPieces [hZeroW [hValue hOutside]]] hw.
have hCoverW:=hw; rewrite hDecomposition in hCoverW.
have [[[hw0 hQ]|[p _ hPiece]]|hR]:=hCoverW.
- have [j [d [hApx hNorm]]]:=hValue hw.
  have hGraph:=(@measure_approximate_jacobian_graph R n v (measure_restrict rho W) m mu
    (partial_function_source_restrict W (partial_function_total F)) w j).2 (ex_intro _ d (conj hApx hNorm)).
  have hj:J0 w=j:=hJ0 w j hGraph.
  exists d,j; split; first exact hApx; split; first exact hNorm.
  left; rewrite -hj; exact:(hZeroW (conj hw hQ)).
- exact:(hPieces p Logic.I hPiece).
- by exfalso; exact:(hOutside hR).
Qed.
