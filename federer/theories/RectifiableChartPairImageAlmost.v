(** Federer (1969), 3.2.22(1), pp. 258–259:
    assemble the image alternative almost everywhere on each
    compact source/target chart pair. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP LipschitzBasic
  NormMetricScaleContinuity EuclideanLebesgueDimensions
  TopologicalBorel EuclideanLebesgueBoxes LinearRankAtLeast MeasureUP MeasureAlmostUP MeasureAlmostBasic HausdorffMeasure
  RectifiableCompactChartsUP RectifiableChartPairPieces CompactRectifiableChartPairs
  RectifiableChartPairCoordinates MetricLipschitzComposition EuclideanFactorizedDifferentialsAlmost
  RectifiableTargetChartBadRank RectifiableParameterChartPoints RectifiableChartPairImagePoint
  RectifiableCoareaImageUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_chart_pair_image_almost]: the
    last paragraph of Federer 3.2.22, p. 259.
    Combine the source chart identities of 3.2.19,
    the actual coordinate differential factorization and the
    target good-or-deficient-rank alternative on A_ij.
    Transport the resulting null exceptions through psi_i
    to P_ij by 2.10.11. No common differentiability
    field or null-preimage assumption is imposed. *)
Theorem rectifiable_chart_pair_image_almost (R:realType) m n mu v
    (lambda:R) (W:set (R_n R n)) (Z:set (R_n R v))
    (K:set (R_n R m)) (C:set (R_n R mu))
    (psi:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (F:inner_metric_space (@euclidean_inner_productP R n)->
      inner_metric_space (@euclidean_inner_productP R v))
    (gamma:inner_metric_space (@euclidean_inner_productP R mu)->
      inner_metric_space (@euclidean_inner_productP R v))
    (G:inner_metric_space (@euclidean_inner_productP R v)->
      inner_metric_space (@euclidean_inner_productP R mu)):
  1<lambda ->is_uniform_compact_rectifiable_chart lambda K psi ->
  is_uniform_compact_rectifiable_chart lambda C gamma ->
  psi @` K `<=` W ->gamma @` C `<=` Z ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W< +oo)%E ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R v)) mu) Z ->
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R v)) mu Z< +oo)%E ->
  is_metric_lipschitz setT F ->is_metric_lipschitz setT G ->
  (forall y,C y ->G (gamma y)=y) ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m)
    (rectifiable_chart_pair_parameters K C psi F gamma)
    [set a|is_rectifiable_coarea_image_point m mu W Z F (psi a)] /\
  measure_almost_everywhere_on (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m)
    (rectifiable_chart_pair_piece K C psi F gamma)
    (is_rectifiable_coarea_image_point m mu W Z F).
Proof.
move=>hLambda hChart hTarget hKW hCZ hW hWFin hZ hZFin hF hG hInverse.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose T:=inner_metric_space (@euclidean_inner_productP R mu).
pose V:=inner_metric_space (@euclidean_inner_productP R v).
pose A:=rectifiable_chart_pair_parameters K C psi F gamma.
pose phi:=fun a:X=>(G (F (psi a)):T).
have hPsi:=metric_lipschitz_of_bound (rectifiable_chart_global_bound hChart).
have hGamma:=metric_lipschitz_of_bound (rectifiable_chart_global_bound hTarget).
have hFPsi:=metric_lipschitz_whole_composite hPsi hF.
have hPhi:is_metric_lipschitz setT phi:=metric_lipschitz_whole_composite hFPsi hG.
have hPsiCont:continuous psi.
  have [L [hL hB]]:=hPsi; apply:(metric_fixed_lipschitz_continuous (ltW hL))=>a b.
  exact:(hB.2 a b Logic.I Logic.I).
have hFCont:continuous F.
  have [L [hL hB]]:=hF; apply:(metric_fixed_lipschitz_continuous (ltW hL))=>a b.
  exact:(hB.2 a b Logic.I Logic.I).
have hGammaCont:continuous gamma.
  have [L [hL hB]]:=hGamma; apply:(metric_fixed_lipschitz_continuous (ltW hL))=>a b.
  exact:(hB.2 a b Logic.I Logic.I).
have hCompact:@compact X A:=compact_rectifiable_chart_pair_parameters
  (rectifiable_chart_compact hChart) (rectifiable_chart_compact hTarget) hPsiCont hFCont hGammaCont.
have hA:measure_measurable (@euclidean_lebesgue_measure R m) A.
  exact:(euclidean_borel_measurable (closed_borel_set (compact_closed (@metric_hausdorff R X) hCompact))).
have hAgreement:forall a,A a ->C (phi a) /\ F (psi a)=gamma (phi a).
  exact:(rectifiable_chart_pair_coordinate_agreement hInverse).
have hPoints:=rectifiable_parameter_chart_points_almost hLambda hChart hKW hW hWFin hF.
have hFactors:=euclidean_factorized_differentials_almost hA hFPsi hPhi hTarget hAgreement.
have hRank:=rectifiable_target_chart_good_or_deficient_rank hLambda hTarget hCZ hZ hZFin hPhi.
pose hm:=euclidean_lebesgue_is_measure R m.
have hAll:=measure_almost_everywhere_and hm
  ((measure_almost_everywhere_on_implication _ _ _).1 hPoints)
  (measure_almost_everywhere_and hm
    ((measure_almost_everywhere_on_implication _ _ _).1 hFactors) hRank).
have hParam:measure_almost_everywhere_on (@euclidean_lebesgue_measure R m) A
    [set a|is_rectifiable_coarea_image_point m mu W Z F (psi a)].
  apply:(measure_almost_everywhere_on_implication _ _ _).2.
  apply:(measure_almost_everywhere_mono hm _ hAll)=>a [hPoint [hFactor hAlternative]] ha.
  have hKa:K a:=ha.1.
  have [H [L [Dt [hH [hL [hDt [hEq hBounds]]]]]]]:=hFactor ha.
  have [hCa hValue]:=hAgreement a ha.
  have hAlt:rectifiable_target_chart_good_parameters Z gamma (phi a) \/ ~linear_rank_at_least L mu.
    have [hGood|hLow]:=hAlternative hCa; first by left.
    right; exact:(hLow L hL).
  exact:(rectifiable_chart_pair_image_point hLambda hChart hKa (hPoint hKa)
    hH hDt (esym hValue) hEq hAlt).
split; first exact hParam.
rewrite rectifiable_chart_pair_image.
exact:(euclidean_lipschitz_almost_pushforward hPsi hParam).
Qed.
