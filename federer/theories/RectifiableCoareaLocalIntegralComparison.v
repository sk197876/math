(** Federer (1969), 3.2.22, pp. 259–260:
    the complete local comparison of a_ij and b_ij. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric LipschitzUP LipschitzBasic
  NormMetricScaleContinuity EuclideanLebesgueDimensions EuclideanLebesgueBoxes TopologicalBorel
  BorelRegularMeasureUP HausdorffClosedCoverAgreement HausdorffMeasure HausdorffFibreCutoffs MappingMultiplicity
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionExtensionUP
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureRestriction MeasurableFunctionUP
  MeasurableRealEmbedding PartialExtendedOrderLoci MeasureNonnegativeIntegral MeasureIntegralBounds
  MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence MeasureIntegralAlmostEquality
  RectifiableCompactChartsUP RectifiableCompactChartLaws RectifiableChartInverseExtension
  RectifiableChartPairPieces RectifiableChartPairCoordinates CompactRectifiableChartPairs MetricLipschitzComposition
  RectifiableCoareaRemainders EuclideanJacobianBorelRepresentatives EuclideanNonStrictCoarea
  CompactInjectiveAreaRepresentative OrdinaryJacobianSubsetRepresentative
  NonnegativeSubsetIntegralComparison SubsetIntegralTotalAgreement RectifiableParameterCoareaBounds
  RectifiableTargetFibreProductBounds MeasureApproximateJacobian TotalScalarCutoff RealMetricBackground ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_coarea_local_integral_comparison]:
    the last display of p. 259 and first three
    displays of p. 260 in Federer 3.2.22.
    Two injective area transformations and ordinary coarea
    give a_ij and b_ij comparable by lambda^(2mu+2m).
    The coordinate comparison contributes 2mu+m and
    the fibre/target-area comparison contributes m.
    No finiteness of either integral is required. The
    measurable cutoff density is a proved intermediate
    premise, discharged before the global application. *)
Theorem rectifiable_coarea_local_integral_comparison (R:realType) m n mu v
    (lambda:R) (W:set (R_n R n)) (K:set (R_n R m)) (C:set (R_n R mu))
    (psi:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (F:inner_metric_space (@euclidean_inner_productP R n)->
      inner_metric_space (@euclidean_inner_productP R v))
    (gamma:inner_metric_space (@euclidean_inner_productP R mu)->
      inner_metric_space (@euclidean_inner_productP R v)) (J0:R_n R n->R):
  (mu<=m)%N ->(1<lambda)%R ->
  is_uniform_compact_rectifiable_chart lambda K psi ->
  is_uniform_compact_rectifiable_chart lambda C gamma ->psi @` K `<=` W ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W< +oo ->
  is_metric_lipschitz setT F ->(forall w,(0<=J0 w)%R) ->
  is_partial_function_total_extension
    (measure_approximate_jacobian (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) W) m mu
      (partial_function_source_restrict W (partial_function_total F))) J0 ->
  @is_measure_measurable_function R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
    [the topologicalType of real_line_metric R]
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
    (partial_function_total (total_scalar_cutoff W J0)) ->
  let P:=rectifiable_chart_pair_piece K C psi F gamma in
  exists a b,
    is_measure_subset_integral (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) P
      (partial_function_total (fun w=>((J0 w)%:E:extended_real_line R))) a /\
    is_measure_integral (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R v)) mu)
      (partial_function_total (fun z=>(@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) (m-mu) (mapping_fibre F P z)
          :extended_real_line R))) b /\
    0<=a /\ 0<=b /\
    a<=(lambda^+(mu+mu+m+m))%R%:E*b /\ b<=(lambda^+(mu+mu+m+m))%R%:E*a.
Proof.
move=>hDim hLambda hChart hTarget hKW hW hWFin hF hJPositive hJ0 hCutMeas P.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose T:=inner_metric_space (@euclidean_inner_productP R mu).
pose V:=inner_metric_space (@euclidean_inner_productP R v).
pose rho:=@hausdorff_measure R Y m.
pose beta:=@hausdorff_measure R V mu.
pose ell:=@euclidean_lebesgue_measure R m.
pose ellT:=@euclidean_lebesgue_measure R mu.
have hr:=@hausdorff_measure_is_measure R Y m.
have hb:=@hausdorff_measure_is_measure R V mu.
have hl:=euclidean_lebesgue_is_measure R m.
have ht:=euclidean_lebesgue_is_measure R mu.
have hPositive:(0<lambda)%R:=lt_trans ltr01 hLambda.
have [G [hG hInverse]]:=uniform_compact_chart_inverse_global_extension hTarget.
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
have hCompactA:@compact X A:=compact_rectifiable_chart_pair_parameters
  (rectifiable_chart_compact hChart) (rectifiable_chart_compact hTarget) hPsiCont hFCont hGammaCont.
have hCompactP:@compact Y P:=compact_rectifiable_chart_pair_piece
  (rectifiable_chart_compact hChart) (rectifiable_chart_compact hTarget) hPsiCont hFCont hGammaCont.
have hA:measure_measurable ell A:=euclidean_borel_measurable
  (closed_borel_set (compact_closed (@metric_hausdorff R X) hCompactA)).
have hP:measure_measurable rho P:=borel_regular_borel_measurable hr
  (@hausdorff_measure_borel_regular R Y m) (closed_borel_set (compact_closed (@metric_hausdorff R Y) hCompactP)).
have hAK:A `<=` K by move=>a [ha _].
have hPW:P `<=` W by move=>w [hw _]; exact:(hKW w hw).
have hPFin:rho P< +oo:=le_lt_trans (measure_mono hr hPW) hWFin.
have hAgreement:forall a,A a ->C (phi a) /\ F (psi a)=gamma (phi a).
  exact:(rectifiable_chart_pair_coordinate_agreement hInverse).
have hImage:P=psi @` A:=@rectifiable_chart_pair_image (R_n R m) (R_n R n) (R_n R mu) (R_n R v) K C psi F gamma.
pose cut:=total_scalar_cutoff W J0.
have hCutNonnegative w:(0<=cut w)%R.
  have [hw|hw]:=pselect (W w).
  - rewrite /cut (total_scalar_cutoff_on J0 hw); exact:(hJPositive w).
  - by rewrite /cut (total_scalar_cutoff_off J0 hw).
have hCutExtended:=measurable_total_real_embedding hr hCutMeas.
have hCutPosE w:0<=(cut w)%:E by rewrite lee_fin; exact:(hCutNonnegative w).
have [a [hASourceCut hANonnegative]]:=nonnegative_total_subset_integral_exists hr hP hCutExtended hCutPosE.
have hASource:is_measure_subset_integral rho P
    (partial_function_total (fun w=>((J0 w)%:E:extended_real_line R))) a.
  have hAgree w:P w ->(cut w)%:E=(J0 w)%:E.
    move=>hw; by rewrite /cut (total_scalar_cutoff_on J0 (hPW w hw)).
  exact:((@subset_integral_total_agreement R [the choiceType of Y] rho P
    (fun w=>((cut w)%:E:extended_real_line R)) (fun w=>((J0 w)%:E:extended_real_line R)) a hAgree).1 hASourceCut).
pose massP:=fun z:V=>(@hausdorff_measure R Y (m-mu) (mapping_fibre F P z):extended_real_line R).
have hMassPMeas:is_measure_measurable_function beta (partial_function_total massP).
  exact:(rectifiable_coarea_fibre_measurability hDim hF hP hPFin).1.
have hMassPPositive z:0<=massP z:=@measure_nonnegative R Y _ (@hausdorff_measure_is_measure R Y (m-mu)) _.
have hMassPAE:measure_almost_everywhere beta (partial_extended_nonnegative_locus (partial_function_total massP)).
  apply:(measure_almost_everywhere_mono hb _ (measure_almost_everywhere_true hb))=>z _.
  exists (massP z); by split.
have hBIntegral:=nonnegative_measurable_function_integral hb hMassPMeas hMassPAE.
pose b:=measure_lower_integral beta (partial_function_total massP).
have hB:is_measure_integral beta (partial_function_total massP) b:=hBIntegral.1.
have hBNonnegative:0<=b:=hBIntegral.2.
have hMassPOff z:~(gamma @` C) z ->massP z=0.
  move=>hNot; have hEmpty:mapping_fibre F P z=set0.
    apply/seteqP; split=>[w [[hSource hTargetValue] hValue]|w []].
    apply:hNot; by rewrite -hValue.
  rewrite /massP hEmpty; exact:(measure_empty (@hausdorff_measure_is_measure R Y (m-mu))).
have hBSubset:is_measure_subset_integral beta (gamma @` C) (partial_function_total massP) b.
  exact:((@subset_integral_total_supported R [the choiceType of V] beta (gamma @` C) massP b hMassPOff).2 hB).
have [Js [hJsB [hJsPositive hJsActual]]]:=euclidean_top_jacobian_borel_representative_exists hPsi.
have [Jp [hJpB [hJpPositive hJpActual]]]:=euclidean_target_jacobian_borel_representative_exists hPhi.
have [Jg [hJgB [hJgPositive hJgActual]]]:=euclidean_top_jacobian_borel_representative_exists hGamma.
have hInjectiveA x y:A x ->A y ->psi x=psi y ->x=y.
  move=>hx hy; exact:(@uniform_compact_chart_injective R m n lambda K psi hChart x y (hAK x hx) (hAK y hy)).
have hAreaSource:=compact_injective_area_representative hPsi hCompactA hInjectiveA hJsActual
  (fun w=>(J0 w)%:E) a.
have hAImage:is_measure_subset_integral rho (psi @` A)
    (partial_function_total (fun w=>((J0 w)%:E:extended_real_line R))) a by rewrite -hImage.
have hAParameter:=hAreaSource.2 hAImage.
have hAreaTarget:=compact_injective_area_representative hGamma (rectifiable_chart_compact hTarget)
  (uniform_compact_chart_injective hTarget) hJgActual massP b.
have hBParameter:=hAreaTarget.2 hBSubset.
pose massA:=fun y:T=>(@hausdorff_measure R X (m-mu) (mapping_fibre phi A y):extended_real_line R).
have [c [hCOld hC]]:=euclidean_non_strict_coarea_formula hDim hPhi hA.
have hCParameter:=(@ordinary_jacobian_subset_representative R m mu mu phi A Jp hPhi hJpActual c).1 hCOld.
have hMassAOff y:~C y ->massA y=0.
  move=>hNot; have hEmpty:mapping_fibre phi A y=set0.
    apply/seteqP; split=>[a0 [ha hValue]|a0 []].
    apply:hNot; have hCy:=(hAgreement a0 ha).1; by rewrite hValue in hCy.
  rewrite /massA hEmpty; exact:(measure_empty (@hausdorff_measure_is_measure R X (m-mu))).
have hCSubset:is_measure_subset_integral ellT C (partial_function_total massA) c.
  exact:((@subset_integral_total_supported R [the choiceType of T] ellT C massA c hMassAOff).2 hC).
have hProductBounds:=@rectifiable_parameter_coarea_product_bounds R m n mu v lambda W K A C
  psi F phi gamma J0 Js Jp hLambda hChart hTarget hAK hKW hW hWFin hF hFPsi hPhi hA hAgreement
  hJPositive hJ0 hJsActual hJpActual.
have hLowerBounds:measure_almost_everywhere_on ell A [set x|
    (J0 (psi x))%:E*(Js x)%:E<=(lambda^+(mu+mu+m))%R%:E*(Jp x)%:E].
  apply:(measure_null_subset hl _ hProductBounds)=>x [hx hNot]; split; first exact hx.
  move=>[hLo _]; apply:hNot.
  change (is_true ((J0 (psi x))%:E*(Js x)%:E<=(lambda^+(mu+mu+m))%R%:E*(Jp x)%:E)).
  by rewrite -!EFinM lee_fin.
have hUpperBounds:measure_almost_everywhere_on ell A [set x|
    (Jp x)%:E<=(lambda^+(mu+mu+m))%R%:E*((J0 (psi x))%:E*(Js x)%:E)].
  apply:(measure_null_subset hl _ hProductBounds)=>x [hx hNot]; split; first exact hx.
  move=>[_ hUp]; apply:hNot.
  change (is_true ((Jp x)%:E<=(lambda^+(mu+mu+m))%R%:E*((J0 (psi x))%:E*(Js x)%:E))).
  by rewrite -!EFinM lee_fin.
have hAC:=subset_total_integral_positive_comparison hl (exprn_gt0 (mu+mu+m) hPositive)
  hAParameter hCParameter hLowerBounds.
have hCA:=subset_total_integral_positive_comparison hl (exprn_gt0 (mu+mu+m) hPositive)
  hCParameter hAParameter hUpperBounds.
have hFibreBounds:=@rectifiable_target_fibre_product_bounds R m n mu v lambda K C psi F gamma G Jg
  hDim hPositive hChart hTarget hInverse hJgActual.
have hBCBounds:measure_almost_everywhere_on ellT C [set y|
    massP (gamma y)*(Jg y)%:E<=(lambda^+m)%R%:E*massA y].
  apply:(measure_almost_everywhere_on_implication _ _ _).2.
  apply:(measure_almost_everywhere_mono ht _ (measure_almost_everywhere_true ht))=>y _ hy.
  exact:(hFibreBounds y hy).1.
have hCBBounds:measure_almost_everywhere_on ellT C [set y|
    massA y<=(lambda^+m)%R%:E*(massP (gamma y)*(Jg y)%:E)].
  apply:(measure_almost_everywhere_on_implication _ _ _).2.
  apply:(measure_almost_everywhere_mono ht _ (measure_almost_everywhere_true ht))=>y _ hy.
  exact:(hFibreBounds y hy).2.
have hBC:=subset_total_integral_positive_comparison ht (exprn_gt0 m hPositive)
  hBParameter hCSubset hBCBounds.
have hCB:=subset_total_integral_positive_comparison ht (exprn_gt0 m hPositive)
  hCSubset hBParameter hCBBounds.
have hKNonnegative:0<=(lambda^+(mu+mu+m))%R%:E by rewrite lee_fin; exact:exprn_ge0 _ (ltW hPositive).
have hMNonnegative:0<=(lambda^+m)%R%:E by rewrite lee_fin; exact:exprn_ge0 _ (ltW hPositive).
have hFinalAB:a<=(lambda^+(mu+mu+m+m))%R%:E*b.
  have hh:=le_trans hAC (lee_wpmul2l hKNonnegative hCB).
  by rewrite muleA -EFinM -exprD in hh.
have hFinalBA:b<=(lambda^+(mu+mu+m+m))%R%:E*a.
  have hh:=le_trans hBC (lee_wpmul2l hMNonnegative hCA).
  by rewrite muleA -EFinM mulrC -exprD in hh.
exists a,b; split; first exact hASource; split; first exact hB.
split; first exact hANonnegative; split; first exact hBNonnegative; by split.
Qed.
