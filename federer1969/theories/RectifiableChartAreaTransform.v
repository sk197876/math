(** Federer (1969), 3.2.20, p. 257: the two
    transformations on an individual compact parameter chart, using
    the actual approximate Jacobian and the exact source fibre counts. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP LipschitzBasic
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionExtensionUP
  PartialZeroExtension MeasureUP MeasureAlmostUP MeasureAlmostEquality MeasureRestriction
  MeasurableFunctionUP MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence
  MeasureIntegralAlmostEquality TopologicalBorel BorelRegularMeasureUP EuclideanLebesgueDimensions
  HausdorffMeasure MappingMultiplicity RectifiableCompactChartsUP RectifiableCompactChartLaws
  MeasureApproximateJacobian RectifiableParameterJacobianChain AreaExtendedTransformIntegrands
  AreaExtendedFiniteMultiplicity EuclideanCompactMultiplicity MappingChartMultiplicity AreaParameterChainIntegrands.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_compact_chart_area_transform]: the two
    equalities in the proof of Federer 3.2.20, p. 257,
    before summing over i. Both ordinary maps are global Lipschitz
    extensions, while J0 merely preserves the intrinsic partial
    approximate-Jacobian graph. The original partial Jacobian is
    not redefined at exceptional points. Arbitrary extended-real
    g and exact signed integral definedness are retained. *)
Theorem rectifiable_compact_chart_area_transform (R : realType) m n k
    (lambda : R) (W : set (R_n R n)) (K : set (R_n R m))
    (psi : R_n R m -> R_n R n) (F : R_n R n -> R_n R k) (J0 : R_n R n -> R) :
  (1<lambda)%R -> is_uniform_compact_rectifiable_chart lambda K psi ->
  psi @` K `<=` W ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W< +oo ->
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R k)) setT F ->
  is_partial_function_total_extension
    (measure_approximate_jacobian (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) W) m m
      (partial_function_source_restrict W (partial_function_total F))) J0 ->
  forall (g : R_n R k -> \bar R) a,
    is_measure_subset_integral (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
      (psi @` K) (partial_function_total (fun w=>g (F w)* (J0 w)%:E : extended_real_line R)) a <->
    is_measure_integral (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R k)) m)
      (partial_function_total (fun z=>g z* @mapping_multiplicity R _ _ F (psi @` K) z : extended_real_line R)) a.
Proof.
move=> hLam hChart hEW hW hFin hF hJ0 g a.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose Z := inner_metric_space (@euclidean_inner_productP R k).
pose mu := @euclidean_lebesgue_measure R m.
pose beta := @hausdorff_measure R Y m.
pose gamma := @hausdorff_measure R Z m.
have hm := euclidean_lebesgue_is_measure R m.
have hb := @hausdorff_measure_is_measure R Y m.
have hPsiBound := rectifiable_chart_global_bound hChart.
have hPsi : @is_metric_lipschitz R X Y setT psi := metric_lipschitz_of_bound hPsiBound.
have hComp : @is_metric_lipschitz R X Z setT (fun x=>F (psi x)).
  have [L [hL hFL]] := hF.
  have hLam0 : (0<lambda)%R := lt_trans ltr01 hLam.
  exists (L*lambda)%R; split; first exact: (mulr_gt0 hL hLam0).
  split; first exact: (mulr_ge0 (ltW hL) (ltW hLam0)).
  move=> x y _ _; apply: le_trans (hFL.2 (psi x) (psi y) I I) _.
  rewrite -mulrA; exact: (ler_wpM2l (ltW hL) (hPsiBound.2 x y I I)).
have hK := rectifiable_chart_compact hChart.
have hKm : measure_measurable mu K :=
  borel_regular_borel_measurable hm (euclidean_lebesgue_borel_regular R m)
    (closed_borel_set (compact_closed (@metric_hausdorff R X) hK)).
have hPsiFinite := euclidean_compact_multiplicity_finite hPsi hK.
have hCompFinite := euclidean_compact_multiplicity_finite hComp hK.
pose G (w : Y) : \bar R := g (F w)* (J0 w)%:E.
have hPsiFormula := @area_extended_finite_multiplicity_transform R m n psi K
  hPsi hKm hPsiFinite G a.
have hCompFormula := @area_extended_finite_multiplicity_transform R m k (fun x=>F (psi x)) K
  hComp hKm hCompFinite g a.
have hChain := rectifiable_parameter_jacobian_chain hLam hChart hEW hW hFin hF hJ0.
have hSource := @area_parameter_chain_integrand_agreement R m n k mu hm K psi F J0 hChain g.
have hInj := @uniform_compact_chart_injective R m n lambda K psi hChart.
have hPsiGraph := @univalent_multiplicity_weight_graph R X Y K psi G hInj.
have hCompGraph z t :
    partial_function_graph (area_extended_target_integrand (fun x=>F (psi x)) K g) z t <->
    partial_function_graph (partial_function_total
      (fun z=>g z* @mapping_multiplicity R Y Z F (psi @` K) z : extended_real_line R)) z t.
  change (g z* @mapping_multiplicity R X Z (fun x=>F (psi x)) K z=t <->
    g z* @mapping_multiplicity R Y Z F (psi @` K) z=t).
  by rewrite (@mapping_multiplicity_injective_chart R X Y Z K psi F z hInj).
split=> hI.
- have hPsiTarget := measure_integral_graph_equivalent
    (fun w t=>iff_sym (hPsiGraph w t)) hI.
  have hPsiSource := hPsiFormula.2 hPsiTarget.
  have hCompSource := measure_integral_almost_equal hm hPsiSource (measure_almost_equal_sym hSource).
  exact: (measure_integral_graph_equivalent hCompGraph (hCompFormula.1 hCompSource)).
- have hCompTarget := measure_integral_graph_equivalent
    (fun z t=>iff_sym (hCompGraph z t)) hI.
  have hCompSource := hCompFormula.2 hCompTarget.
  have hPsiSource := measure_integral_almost_equal hm hCompSource hSource.
  exact: (measure_integral_graph_equivalent hPsiGraph (hPsiFormula.1 hPsiSource)).
Qed.
