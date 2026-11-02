(** Federer (1969), 3.2.20, p. 257: the compact-chart
    transformation with weight one supplies the measurable intrinsic
    Jacobian density on each compact image. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP LipschitzBasic
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionExtensionUP
  ExtendedRealOrderTopology MeasureUP MeasureRestriction MeasureIntegralUP MeasureSubsetIntegral
  MeasureIntegralGraphEquivalence TopologicalBorel BorelRegularMeasureUP EuclideanLebesgueDimensions
  HausdorffMeasure MappingMultiplicity RectifiableCompactChartsUP RectifiableCompactChartLaws
  MeasureApproximateJacobian EuclideanAreaFormula MappingChartMultiplicity RectifiableChartAreaTransform.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_compact_chart_jacobian_integral]: supporting
    measurable density and unweighted identity on each chart in
    Federer 3.2.20, p. 257. Both integrals exist; this
    assertion is proved before assuming global measurability of the
    approximate Jacobian. The auxiliary J0 preserves its exact graph. *)
Theorem rectifiable_compact_chart_jacobian_integral (R : realType) m n k
    (lambda : R) (W : set (R_n R n)) (K : set (R_n R m))
    (psi : R_n R m -> R_n R n) (F : R_n R n -> R_n R k) (J0 : R_n R n -> R) :
  (1<lambda)%R -> is_uniform_compact_rectifiable_chart lambda K psi -> psi @` K `<=` W ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W< +oo ->
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R k)) setT F ->
  is_partial_function_total_extension
    (measure_approximate_jacobian (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) W) m m
      (partial_function_source_restrict W (partial_function_total F))) J0 ->
  exists a,
    is_measure_subset_integral (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
      (psi @` K) (partial_function_total (fun w=>(J0 w)%:E : extended_real_line R)) a /\
    is_measure_integral (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R k)) m)
      (partial_function_total (fun z=>(@mapping_multiplicity R _ _ F (psi @` K) z : extended_real_line R))) a.
Proof.
move=> hLam hChart hEW hW hFin hF hJ0.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose Z := inner_metric_space (@euclidean_inner_productP R k).
have hPsiBound := rectifiable_chart_global_bound hChart.
have hComp : @is_metric_lipschitz R X Z setT (fun x=>F (psi x)).
  have [L [hL hFL]] := hF.
  have hLam0 : (0<lambda)%R := lt_trans ltr01 hLam.
  exists (L*lambda)%R; split; first exact: (mulr_gt0 hL hLam0).
  split; first exact: (mulr_ge0 (ltW hL) (ltW hLam0)).
  move=> x y _ _; apply: le_trans (hFL.2 (psi x) (psi y) I I) _.
  rewrite -mulrA; exact: (ler_wpM2l (ltW hL) (hPsiBound.2 x y I I)).
have hKm : measure_measurable (@euclidean_lebesgue_measure R m) K :=
  borel_regular_borel_measurable (euclidean_lebesgue_is_measure R m) (euclidean_lebesgue_borel_regular R m)
    (closed_borel_set (compact_closed (@metric_hausdorff R X) (rectifiable_chart_compact hChart))).
have [a [hSource hCount]] := euclidean_area_formula hComp hKm.
have hInj := @uniform_compact_chart_injective R m n lambda K psi hChart.
have hCountFE : is_measure_integral (@hausdorff_measure R Z m)
    (partial_function_total (fun z=>(@mapping_multiplicity R Y Z F (psi @` K) z : extended_real_line R))) a.
  apply: (@measure_integral_graph_equivalent R Z (@hausdorff_measure R Z m) _ _ a _ hCount)=> z t.
  change (@mapping_multiplicity R X Z (fun x=>F (psi x)) K z=t <->
    @mapping_multiplicity R Y Z F (psi @` K) z=t).
  by rewrite (@mapping_multiplicity_injective_chart R X Y Z K psi F z hInj).
have hFormula := @rectifiable_compact_chart_area_transform R m n k lambda W K psi F J0
  hLam hChart hEW hW hFin hF hJ0 (fun _=>1) a.
have hT : (fun z=>1* @mapping_multiplicity R Y Z F (psi @` K) z : extended_real_line R)=
    (fun z=>(@mapping_multiplicity R Y Z F (psi @` K) z : extended_real_line R)).
  by apply: funext=> z; rewrite mul1e.
have hS : (fun w=>1* (J0 w)%:E : extended_real_line R)=
    (fun w=>(J0 w)%:E : extended_real_line R).
  by apply: funext=> w; rewrite mul1e.
rewrite hT hS in hFormula.
exists a; split; [exact: hFormula.2 hCountFE|exact hCountFE].
Qed.
