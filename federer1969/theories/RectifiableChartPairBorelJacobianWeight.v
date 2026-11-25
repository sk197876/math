(** Federer (1969), 3.2.22, pp. 259–260:
    Borel approximate densities on compact chart pairs. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP LipschitzBasic
  NormMetricScaleContinuity EuclideanLebesgueDimensions TopologicalBorel EuclideanLebesgueBoxes
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionExtensionUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureRestriction HausdorffMeasure MeasureApproximateJacobian
  RectifiableCompactChartsUP RectifiableChartPairPieces CompactRectifiableChartPairs
  RectifiableChartPairCoordinates MetricLipschitzComposition RectifiableChartInverseExtension
  CoareaChartJacobianWeight RectifiableBorelChartJacobianWeight BorelFunctionUP RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_chart_pair_borel_jacobian_weight]:
    the source Jacobian comparison in Federer 3.2.22,
    p. 259, with its implicit measurability justified.
    Exact Borel representatives for the ordinary coordinate
    and target-chart Jacobians give a Borel product.
    Factorization proves agreement with J_mu(F composed psi)
    almost everywhere on A_ij. Pull back through the
    source inverse and retain both lambda^mu bounds on P_ij. *)
Theorem rectifiable_chart_pair_borel_jacobian_weight (R:realType) m n mu v
    (lambda:R) (W:set (R_n R n)) (K:set (R_n R m)) (C:set (R_n R mu))
    (psi:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (F:inner_metric_space (@euclidean_inner_productP R n)->
      inner_metric_space (@euclidean_inner_productP R v))
    (gamma:inner_metric_space (@euclidean_inner_productP R mu)->
      inner_metric_space (@euclidean_inner_productP R v)) (J0:R_n R n->R):
  1<lambda ->is_uniform_compact_rectifiable_chart lambda K psi ->
  is_uniform_compact_rectifiable_chart lambda C gamma ->psi @` K `<=` W ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W< +oo)%E ->
  is_metric_lipschitz setT F ->
  is_partial_function_total_extension
    (measure_approximate_jacobian (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) W) m mu
      (partial_function_source_restrict W (partial_function_total F))) J0 ->
  exists h:inner_metric_space (@euclidean_inner_productP R n)->real_line_metric R,
    is_borel_function h /\ (forall w,0<=h w) /\
    measure_almost_everywhere_on (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m)
      (rectifiable_chart_pair_piece K C psi F gamma) [set w|
        (lambda^+mu)^-1*J0 w<=h w /\ h w<=lambda^+mu*J0 w].
Proof.
move=>hLambda hChart hTarget hKW hW hWFin hF hJ0.
have [G [hG hInverse]]:=uniform_compact_chart_inverse_global_extension hTarget.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose T:=inner_metric_space (@euclidean_inner_productP R mu).
pose V:=inner_metric_space (@euclidean_inner_productP R v).
pose A:=rectifiable_chart_pair_parameters K C psi F gamma.
pose phi:=fun a:X=>(G (F (psi a)):T).
have hPsi:=metric_lipschitz_of_bound (rectifiable_chart_global_bound hChart).
have hGamma:=metric_lipschitz_of_bound (rectifiable_chart_global_bound hTarget).
have hFPsi:=metric_lipschitz_whole_composite hPsi hF.
have hPhi:is_metric_lipschitz setT phi:=metric_lipschitz_whole_composite hFPsi (metric_lipschitz_of_bound hG).
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
have [J [hJB [hJNonnegative hJActual]]]:=coarea_chart_jacobian_borel_weight_exists
  hA hFPsi hPhi hTarget hAgreement.
have hAK:A `<=` K by move=>a [ha _].
have [h [hB [hNonnegative hBounds]]]:=rectifiable_borel_chart_jacobian_weight
  hLambda hChart hAK hKW hW hWFin hF hJ0 hJB hJNonnegative hJActual.
exists h; split; first exact hB; split; first exact hNonnegative.
by rewrite rectifiable_chart_pair_image.
Qed.
