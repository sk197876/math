(** Federer (1969), 3.2.22(3), p. 260:
    a finite almost-everywhere bound for the intrinsic
    Jacobian preserves the finite signed variation. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  NormDifferentialUP NormDifferentialLipschitzBound LipschitzUP MetricLipschitzComposition
  EuclideanLinearJacobian EuclideanExteriorComposition EuclideanLebesgueDimensions
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionExtensionUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureRestriction HausdorffMeasure
  RectifiableSetUP RectifiableCompactChartsUP RectifiableCompactCharts RectifiableParameterJacobianBounds
  RectifiableParameterChartPoints MeasureApproximateJacobian TotalScalarCutoff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_coarea_jacobian_cutoff_bounded_almost]:
    the bounded-Jacobian control implicit in the signed
    standard approximation in Federer 3.2.22(3), p. 260,
    following 3.2.12, p. 250. Fixed distortion-two
    charts and the differential Lipschitz bound give
    the sufficient finite constant 2^q(2 Lip F)^q.
    A sharp constant is unnecessary. Undefined public
    Jacobian points are not filled; this bounds an
    auxiliary cutoff representative only almost everywhere. *)
Theorem rectifiable_coarea_jacobian_cutoff_bounded_almost (R:realType) m n k q
    (W:set (R_n R n))
    (F:inner_metric_space (@euclidean_inner_productP R n)->
      inner_metric_space (@euclidean_inner_productP R k)) (J0:R_n R n->R):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  is_metric_lipschitz setT F ->
  is_partial_function_total_extension
    (measure_approximate_jacobian (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) W) m q
      (partial_function_source_restrict W (partial_function_total F))) J0 ->
  exists C:R,0<C /\ measure_almost_everywhere (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) [set w|total_scalar_cutoff W J0 w<=C].
Proof.
move=>hRect hW hF hJ0.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose Z:=inner_metric_space (@euclidean_inner_productP R k).
pose rho:=@hausdorff_measure R Y m.
have hr:=@hausdorff_measure_is_measure R Y m.
have [L [hL hBound]]:=hF.
have hTwo:1<(2:R) by rewrite ltr1n.
have hTwoPositive:0<(2:R) by rewrite ltr0n.
have [K [psi hCover]]:=@federer_3_2_18 R m n 2 W hRect hW hTwo.
pose C:=(2:R)^+q*(L*2)^+q.
have hC:0<C:=mulr_gt0 (exprn_gt0 q hTwoPositive) (exprn_gt0 q (mulr_gt0 hL hTwoPositive)).
have hEach i:measure_almost_everywhere rho [set w|(psi i @` K i) w ->J0 w<=C].
  have hChart:=(hCover.1 i).1.
  have hParameters:=@rectifiable_parameter_jacobian_bounds R m n k q 2 W (K i) (psi i) F J0
    hTwo hChart (hCover.1 i).2 hW hRect.2 hF hJ0.
  have hCompositeBound:@is_metric_lipschitz_bound R X Z setT (fun a=>F (psi i a)) (L*2).
    exact:(metric_lipschitz_composition_bound (fun _ _=>Logic.I)
      (rectifiable_chart_global_bound hChart) hBound).
  have hPoint:measure_almost_everywhere_on (@euclidean_lebesgue_measure R m) (K i)
      [set a|J0 (psi i a)<=C].
    apply:(measure_almost_everywhere_on_implication _ _ _).2.
    apply:(measure_almost_everywhere_mono (euclidean_lebesgue_is_measure R m) _
      ((measure_almost_everywhere_on_implication _ _ _).1 hParameters))=>a hParameter ha.
    have [D [H [hD [hH [hLower hUpper]]]]]:=hParameter ha.
    have hVector:forall v,inner_norm (@euclidean_inner_productP R k) (H v)<=
        (L*2)*inner_norm (@euclidean_inner_productP R m) v.
      apply:(@norm_differential_global_lipschitz_bound R (R_n R m) (R_n R k)
        (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R k))
        (inner_norm_real_norm (@euclidean_inner_productP R m))
        (inner_norm_real_norm (@euclidean_inner_productP R k)) (fun a=>F (psi i a)) a H (L*2) hH).
      move=>a0 b0; exact:(hCompositeBound.2 a0 b0 Logic.I Logic.I).
    have hJacobian:=euclidean_exterior_jacobian_vector_bound_power q (ltW (mulr_gt0 hL hTwoPositive)) hVector.
    have hPowPositive:0<(2:R)^+q:=exprn_gt0 q hTwoPositive.
    have hScaled:=ler_wpM2l (ltW hPowPositive) hLower.
    have hNonzero:(2:R)^+q!=0 by rewrite(gt_eqF hPowPositive).
    rewrite mulrA (mulfV hNonzero) mul1r in hScaled.
    exact:(le_trans hScaled (ler_wpM2l (ltW hPowPositive) hJacobian)).
  have hLip:@is_metric_lipschitz R X Y setT (psi i).
    exists 2; split; first exact hTwoPositive; exact:rectifiable_chart_global_bound hChart.
  exact:((measure_almost_everywhere_on_implication _ _ _).1
    (euclidean_lipschitz_almost_pushforward hLip hPoint)).
have hAll:=@measure_almost_everywhere_countable R [the choiceType of Y]
  [the choiceType of (nat:Type)] rho hr setT
  (fun i=>[set w|(psi i @` K i) w ->J0 w<=C]) (countableP _) (fun i _=>hEach i).
have hNotR:measure_almost_everywhere rho (~` (W `\` (\bigcup_i psi i @` K i))).
  rewrite /measure_almost_everywhere setCK; exact hCover.2.2.
exists C; split; first exact hC.
apply:(measure_almost_everywhere_mono hr _ (measure_almost_everywhere_and hr hAll hNotR))=>w [hCharts hOutside].
change (is_true (total_scalar_cutoff W J0 w<=C)).
have [hw|hw]:=pselect (W w).
- rewrite (total_scalar_cutoff_on J0 hw).
  have hIn:(\bigcup_i psi i @` K i) w.
    apply:contrapT=>hNot; apply:hOutside; by split.
  have [i _ hPi]:=hIn; exact:(hCharts i Logic.I hPi).
- rewrite (total_scalar_cutoff_off J0 hw); exact:ltW hC.
Qed.
