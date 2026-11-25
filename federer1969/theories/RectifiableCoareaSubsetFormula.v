(** Federer (1969), 3.2.22, p. 260:
    the characteristic-function coarea identity on
    every measurable subset of W, with the original
    intrinsic approximate Jacobian. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionExtensionUP
  MeasureUP MeasureRestriction HausdorffMeasure MeasureApproximateJacobian RectifiableSetUP
  MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralUniqueness
  RectifiableCoareaSubsetComparison ExtendedPowerGeometricSqueeze MappingMultiplicity ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_coarea_subset_formula]:
    the penultimate display and following measurable-
    subset sentence in Federer 3.2.22, p. 260.
    Two global distortion bounds hold for every
    lambda>1. The proved extended-real power squeeze
    forces equality, including zero and infinite
    values. Use the H^mu outer measure of assertion (3)
    on p. 258; the H^m in the penultimate display
    on p. 260 is a typographical consistency correction
    local to this project, absent from the erratum.
    The approximate Jacobian is still that
    relative to W even when A is a proper subset. *)
Theorem rectifiable_coarea_subset_formula (R:realType) m n mu v
    (W A:set (R_n R n)) (Z:set (R_n R v))
    (F:inner_metric_space (@euclidean_inner_productP R n)->
      inner_metric_space (@euclidean_inner_productP R v)) (J0:R_n R n->R):
  (mu<=m)%N ->A `<=` W ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) A ->
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
  exists a,
    is_measure_subset_integral (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) A
      (partial_function_total (fun w=>((J0 w)%:E:extended_real_line R))) a /\
    is_measure_integral (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R v)) mu)
      (partial_function_total (fun z=>(@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) (m-mu) (mapping_fibre F A z)
          :extended_real_line R))) a.
Proof.
move=>hDim hAW hA hRectW hW hRectZ hZ hF hRange hJPositive hJ0.
have hCompare lambda (hLambda:(1<lambda)%R):=
  rectifiable_coarea_subset_comparison hDim hLambda hAW hA hRectW hW hRectZ hZ hF hRange hJPositive hJ0.
have hTwo:(1<(2:R))%R by rewrite ltr1n.
have [a [b [hAIntegral [hBIntegral [hAPos [hBPos _]]]]]]:=hCompare 2%R hTwo.
have hBounds lambda (hLambda:(1<lambda)%R):
    a<=(lambda^+(mu+mu+m+m))%R%:E*b /\ b<=(lambda^+(mu+mu+m+m))%R%:E*a.
  have [a0 [b0 [hA0 [hB0 [_ [_ hResult]]]]]]:=hCompare lambda hLambda.
  have hEqA:a0=a:=measure_integral_unique hA0 hAIntegral.
  have hEqB:b0=b:=measure_integral_unique hB0 hBIntegral.
  by rewrite hEqA hEqB in hResult.
have hAB:a<=b:=@extended_power_geometric_squeeze R b a (mu+mu+m+m) hBPos
  (fun lambda hLambda=>(hBounds lambda hLambda).1).
have hBA:b<=a:=@extended_power_geometric_squeeze R a b (mu+mu+m+m) hAPos
  (fun lambda hLambda=>(hBounds lambda hLambda).2).
have hEqual:b=a by apply/eqP; rewrite eq_le hBA hAB.
exists a; split; first exact hAIntegral; by rewrite -hEqual.
Qed.
