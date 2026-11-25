(** Federer (1969), 3.2.22(3), pp. 258, 260:
    the full weighted coarea identity for total auxiliary
    weights zero outside the original source. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionExtensionUP PartialZeroExtension PartialDensityProduct
  MeasureUP MeasureBasic MeasureRestriction MeasureAlmostUP MeasureAlmostBasic PartialExtendedOrderLoci
  MeasurableFunctionUP MeasurableRealEmbedding MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralUniqueness
  MeasureDensityUP MeasureDensity DensityCharacteristicIntegral
  RectifiableSetUP HausdorffMeasure HausdorffFibreCutoffs MeasureApproximateJacobian
  RectifiableCoareaSubsetFormula RectifiableCoareaRemainders RectifiableCoareaJacobianMeasurable RectifiableCoareaJacobianAlmostBound
  NonnegativePartialRealExtension TotalScalarCutoff DisjointScalarCutoffSeries SubsetIntegralTotalAgreement
  MappingMultiplicity SupportedCoareaNonnegative SupportedCoareaSigned ParameterizedIntegral ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_coarea_supported_integrable_weights]:
    the standard approximation completing Federer
    3.2.22(3), p. 260. Every characteristic
    coarea identity and fibre measurability law follows
    from the printed rectifiability hypotheses. Positive
    and negative parts give both actual integral graphs;
    a finite almost-everywhere Jacobian bound proves
    the signed differences defined. Either infinite
    signed value is allowed, with no summability premise. *)
Theorem rectifiable_coarea_supported_integrable_weights (R:realType) m n mu v
    (W:set (R_n R n)) (Z:set (R_n R v))
    (F:inner_metric_space (@euclidean_inner_productP R n)->
      inner_metric_space (@euclidean_inner_productP R v)) (J0:R_n R n->R)
    (u:R_n R n->extended_real_line R):
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
  (forall w,(0<=J0 w)%R) ->
  is_partial_function_total_extension
    (measure_approximate_jacobian (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) W) m mu
      (partial_function_source_restrict W (partial_function_total F))) J0 ->
  is_measure_integrable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) (partial_function_total u) ->
  (forall w,~W w ->u w=0) ->
  exists a,is_measure_integral (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m)
      (partial_density_product (partial_function_total u)
        (partial_function_total (fun w=>((total_scalar_cutoff W J0 w)%:E:extended_real_line R)))) a /\
    is_measure_integral (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R v)) mu)
      (parameterized_integral (@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) (m-mu))
        (fun z=>partial_function_zero_extension (0:extended_real_line R) [set w|F w=z]
          (partial_function_total u))) a.
Proof.
move=>hDim hRectW hW hRectZ hZ hF hRange hJPositive hJ0 hU hOff.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R v).
pose rho:=@hausdorff_measure R X m.
pose alpha:=@hausdorff_measure R Y mu.
pose beta:=@hausdorff_measure R X (m-mu).
have hr:=@hausdorff_measure_is_measure R X m.
have ha:=@hausdorff_measure_is_measure R Y mu.
have hb:=@hausdorff_measure_is_measure R X (m-mu).
pose p:=total_scalar_cutoff W J0.
pose d:=partial_function_total (fun w=>((p w)%:E:extended_real_line R)).
pose nu:=measure_with_density rho d.
have hDensity:=measure_with_density_laws rho d.
have hPositive w:(0<=p w)%R:=nonnegative_scalar_cutoff W hJPositive w.
have hDAE:measure_almost_everywhere rho (partial_extended_nonnegative_locus d).
  apply:(measure_almost_everywhere_mono hr _ (measure_almost_everywhere_true hr))=>w _.
  exists (p w)%:E; split; first reflexivity; by rewrite lee_fin.
have hn:is_measure nu:=measure_with_density_is_measure hr hDAE.
have hCutMeas:=rectifiable_coarea_jacobian_cutoff_measurable hRectW hW hRectZ hZ hF hRange hJPositive hJ0.
have hDMeas:is_measure_measurable_function rho d:=measurable_total_real_embedding hr hCutMeas.
have hMeasTransfer A:measure_measurable rho A ->measure_measurable nu A.
  exact:(measure_with_density_measurable hr hDAE).
have hCharacteristic A (hAW:A `<=` W) (hA:measure_measurable rho A):
    is_measure_integral alpha (partial_function_total
      (fun z=>(beta (mapping_fibre F A z):extended_real_line R))) (nu A).
  have [a [hSource hTarget]]:=rectifiable_coarea_subset_formula hDim hAW hA hRectW hW hRectZ hZ
    hF hRange hJPositive hJ0.
  have hNuIntegral:=@measurable_density_subset_integral R [the choiceType of X] rho nu hr d A
    hDensity hDAE hDMeas hA.
  have hAgreement w:A w ->(J0 w)%:E=(p w)%:E.
    move=>hw; by rewrite /p (total_scalar_cutoff_on J0 (hAW w hw)).
  have hSourceCut:=(@subset_integral_total_agreement R [the choiceType of X] rho A
    (fun w=>((J0 w)%:E:extended_real_line R)) (fun w=>((p w)%:E:extended_real_line R)) a hAgreement).1 hSource.
  have hValue:a=nu A:=measure_integral_unique hSourceCut hNuIntegral.
  by rewrite -hValue.
have hFibre A (hAW:A `<=` W) (hA:measure_measurable rho A):
    measure_almost_everywhere alpha [set z|measure_measurable beta (mapping_fibre F A z)].
  have hFinite:rho A< +oo:=le_lt_trans (measure_mono hr hAW) hRectW.2.
  exact:(rectifiable_coarea_fibre_measurability hDim hF hA hFinite).2.
have hNonnegative (v0:X->extended_real_line R) (hV:is_measure_measurable_function rho (partial_function_total v0))
    (hVPositive:forall w,0<=v0 w) (hVOff:forall w,~W w ->v0 w=0):=
  supported_coarea_nonnegative_integral hr hn hb ha hMeasTransfer hCharacteristic hFibre hV hVPositive hVOff.
have [C [hC hAlmostBound]]:=rectifiable_coarea_jacobian_cutoff_bounded_almost hRectW hW hF hJ0.
have hBound:measure_almost_everywhere rho [set w|forall j,partial_function_graph d w j ->j<=C%:E].
  apply:(measure_almost_everywhere_mono hr _ hAlmostBound)=>w hBw j hj.
  change ((p w)%:E=j) in hj; rewrite -hj lee_fin; exact hBw.
exact:(supported_coarea_signed_integral hr hn hb ha hDensity hDMeas hDAE
  (ex_intro _ C (conj hC hBound)) hNonnegative hU hOff).
Qed.
