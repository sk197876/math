(** Federer (1969), 3.2.22(3), p. 258:
    restore the original partial map, original weight
    and the printed outer integral over Z. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP LipschitzBasic
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionPostcomposition PartialFunctionExtensionUP
  PartialMetricLipschitz EuclideanPartialLipschitzExtension PartialMappingMultiplicity
  PartialZeroExtension PartialDensityProduct MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic
  MeasureAlmostEquality MeasurableZeroExtension MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence MeasureIntegralAlmostEquality
  HausdorffMeasure RectifiableSetUP MeasureApproximateJacobian NonnegativePartialRealExtension TotalScalarCutoff
  RectifiableApproximateJacobianValues ZeroExtendedDensityWeightAgreement SupportedPartialWeightExtension
  SupportedWeightGraphLaws RectifiableCoareaSupportedWeights RectifiableCoareaIntegrands PartialFibreIntegralTargetCutoff
  ParameterizedIntegral ParameterizedIntegralLaws ExtendedRealOrderTopology RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_partial_coarea_integrable_weights]:
    the complete weighted equality in Federer 3.2.22(3),
    p. 258, with the standard approximation on p. 260
    fully discharged. Both f and g retain exactly W
    as their original domain. The actual intrinsic
    Jacobian is not totalized, and every inner integral
    has precisely its actual signed integrability domain.
    The printed extended-real weights include either
    infinite integral value, while definedness of each
    signed difference remains part of the integral laws. *)
Theorem rectifiable_partial_coarea_integrable_weights (R:realType) m n mu v
    (W:set (R_n R n)) (Z:set (R_n R v))
    (f:partial_function (R_n R n) (R_n R v))
    (g:partial_function (R_n R n) (extended_real_line R)):
  (mu<=m)%N ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) mu Z ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) Z ->
  partial_function_domain f=W ->
  (exists L,@is_partial_metric_lipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R v)) f L) ->
  partial_function_range f `<=` Z ->partial_function_domain g=W ->
  is_measure_integrable (measure_restrict (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W) g ->
  exists a,is_measure_integral (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m)
      (rectifiable_coarea_source_integrand m mu W f g) a /\
    is_measure_subset_integral (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R v)) mu) Z
      (rectifiable_coarea_fibre_integral m mu f g) a.
Proof.
move=>hDim hRectW hW hRectZ hZ hDomain [L hLip] hRange hGDomain hGIntegral.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R v).
pose rho:=@hausdorff_measure R X m.
pose alpha:=@hausdorff_measure R Y mu.
pose beta:=@hausdorff_measure R X (m-mu).
have hr:=@hausdorff_measure_is_measure R X m.
have hb:=@hausdorff_measure_is_measure R X (m-mu).
have [F [hBound hEq]]:=euclidean_partial_lipschitz_global_extension hLip.
rewrite hDomain in hEq.
have hF:=metric_lipschitz_of_bound hBound.
have hExt:is_partial_function_total_extension f F.
  move=>x y hxy; rewrite hEq in hxy; exact hxy.2.
have hImage:forall w,W w ->Z (F w).
  move=>w hw; have hGraph:partial_function_graph f w (F w) by rewrite hEq; split.
  apply:hRange; by exists w.
have [u [hU [hOn [hOff hGGraph]]]]:=supported_partial_integrable_weight_extension hr hW hGDomain hGIntegral.
pose f0:=partial_function_source_restrict W (partial_function_total F).
pose d:=measure_approximate_jacobian (measure_restrict rho W) m mu f0.
have hNonnegative w j:partial_function_graph d w j ->(0<=j)%R.
  exact:(@measure_approximate_jacobian_nonnegative R n v (measure_restrict rho W) m mu f0 w j).
have [J0 [hJPositive hJ0]]:=nonnegative_partial_real_extension hNonnegative.
pose p:=total_scalar_cutoff W J0.
have [a [hSource hTarget]]:=rectifiable_coarea_supported_integrable_weights hDim hRectW hW hRectZ hZ
  hF hImage hJPositive hJ0 hU hOff.
have hProductGraph w z:partial_function_graph (partial_density_product (partial_function_total u)
      (partial_function_total (fun w=>((p w)%:E:extended_real_line R)))) w z <->
    partial_function_graph (partial_function_total (fun w=>(u w*(p w)%:E:extended_real_line R))) w z.
  rewrite partial_density_product_graph; split.
  - move=>[s [t [hs [ht hValue]]]].
    change (u w*(p w)%:E=z); by rewrite (hs:u w=s) (ht:(p w)%:E=t).
  - move=>hValue; exists (u w),(p w)%:E; by split; last split.
have hSourceTotal:=measure_integral_graph_equivalent hProductGraph hSource.
have hValues:=@rectifiable_approximate_jacobian_values_almost R m n v mu W F hRectW hW hF.
have hDomainD:measure_almost_everywhere_on rho W (partial_function_domain d).
  apply:(measure_null_subset hr _ hValues)=>w [hw hNot]; split; first exact hw.
  move=>[j hj]; apply:hNot; exists j; exact:(@measure_approximate_jacobian_graph R n v (measure_restrict rho W) m mu f0 w j).2 hj.
have hZeroDomain:measure_almost_everywhere rho
    (partial_function_domain (partial_function_zero_extension (0%R:real_line_metric R) W d)).
  exact:((@zero_extension_relative_domain R [the choiceType of X] (real_line_metric R) rho 0%R W d).1 hDomainD).
have hCutExt:is_partial_function_total_extension
    (partial_function_zero_extension (0%R:real_line_metric R) W d) p.
  move=>w j hj; have [hw|hw]:=pselect (W w).
  - rewrite /p (total_scalar_cutoff_on J0 hw).
    exact:(hJ0 w j ((partial_function_zero_extension_on _ _ _ hw).1 hj)).
  - have hj0:=(partial_function_zero_extension_off _ _ _ hw).1 hj.
    by rewrite /p (total_scalar_cutoff_off J0 hw) hj0.
have hAgreement:=zero_extended_density_weight_agreement hr u hZeroDomain hCutExt.
have hSourceApprox:=measure_integral_almost_equal hr hSourceTotal (MeasureAlmostEquality.measure_almost_equal_sym hAgreement).
have hWeightGraph:=@supported_weight_density_cutoff_graph R (R_n R n) W g
  (extended_measure_approximate_jacobian (measure_restrict rho W) m mu f0) u hOn.
have hSourceOriginal:=measure_integral_graph_equivalent (fun w z=>iff_sym (hWeightGraph w z)) hSourceApprox.
have hFibreGraph z w t:
    partial_function_graph (partial_function_zero_extension (0:extended_real_line R)
      [set w|F w=z] (partial_function_total u)) w t <->
    partial_function_graph (partial_function_zero_extension (0:extended_real_line R)
      (partial_mapping_fibre f z) g) w t.
  rewrite (@partial_mapping_fibre_total_extension (R_n R n) (R_n R v) f F z hExt) hDomain.
  exact:(@supported_weight_fibre_graph R (R_n R n) (R_n R v) W F g u hOn hOff z w t).
have hParameterGraph:=@parameterized_integral_graph_equivalent R (R_n R v) [the choiceType of X] beta _ _ hFibreGraph.
have hTargetOriginal:=measure_integral_graph_equivalent hParameterGraph hTarget.
have hRangeGraph w z:partial_function_graph f w z ->Z z.
  move=>hwz; apply:hRange; by exists w.
have hTargetCut:=@partial_fibre_integral_target_cutoff_graph R [the choiceType of X] Y beta hb f g Z hRangeGraph.
exists a; split.
- rewrite /rectifiable_coarea_source_integrand hEq; exact hSourceOriginal.
- exact:(measure_integral_graph_equivalent (fun z b=>iff_sym (hTargetCut z b)) hTargetOriginal).
Qed.

(** Source for [rectifiable_partial_coarea_real_integrable_weights]:
    real-valued specialization of Federer 3.2.22(3),
    p. 258. Every H^m restricted to W integrable
    real-valued weight satisfies the weighted identity with
    the actual intrinsic mu-Jacobian and actual original
    fibres. Real integrability allows a signed infinite
    integral. No finite-to-one, rank, derivative-field,
    Jacobian-measurability or summability premise is added. *)
Theorem rectifiable_partial_coarea_real_integrable_weights (R:realType) m n mu v
    (W:set (R_n R n)) (Z:set (R_n R v))
    (f:partial_function (R_n R n) (R_n R v))
    (g:partial_function (R_n R n) (real_line_metric R)):
  (mu<=m)%N ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) mu Z ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) Z ->
  partial_function_domain f=W ->
  (exists L,@is_partial_metric_lipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R v)) f L) ->
  partial_function_range f `<=` Z ->partial_function_domain g=W ->
  let ge:=partial_function_postcompose g (fun r=>(r%:E:extended_real_line R)) in
  is_measure_integrable (measure_restrict (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W) ge ->
  exists a,is_measure_integral (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m)
      (rectifiable_coarea_source_integrand m mu W f ge) a /\
    is_measure_subset_integral (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R v)) mu) Z
      (rectifiable_coarea_fibre_integral m mu f ge) a.
Proof.
move=>hDim hRectW hW hRectZ hZ hDomain hLip hRange hGDomain ge hIntegral.
have hGeDomain:partial_function_domain ge=W by rewrite /ge partial_function_postcompose_domain.
exact:(rectifiable_partial_coarea_integrable_weights hDim hRectW hW hRectZ hZ hDomain hLip hRange hGeDomain hIntegral).
Qed.

(** Source for [federer_3_2_22_3]: the complete
    assertion (3) of Federer 3.2.22, p. 258,
    which prints an extended-real-valued weight g.
    Every such integrable original-domain weight obeys
    the actual weighted coarea identity. Both signed
    infinite integral values and the exact inner
    integrability domains are retained. The outer
    measure is H^mu as in assertion (3); the H^m
    printed in the penultimate display on p. 260
    is a local typographical correction, not an entry
    in Federer's erratum. No summability or further
    derivative, rank or measurability premise is added. *)
Theorem federer_3_2_22_3 (R:realType) m n mu v
    (W:set (R_n R n)) (Z:set (R_n R v))
    (f:partial_function (R_n R n) (R_n R v))
    (g:partial_function (R_n R n) (extended_real_line R)):
  (mu<=m)%N ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) mu Z ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) Z ->
  partial_function_domain f=W ->
  (exists L,@is_partial_metric_lipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R v)) f L) ->
  partial_function_range f `<=` Z ->partial_function_domain g=W ->
  is_measure_integrable (measure_restrict (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W) g ->
  exists a,is_measure_integral (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m)
      (rectifiable_coarea_source_integrand m mu W f g) a /\
    is_measure_subset_integral (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R v)) mu) Z
      (rectifiable_coarea_fibre_integral m mu f g) a.
Proof.
exact:rectifiable_partial_coarea_integrable_weights.
Qed.
