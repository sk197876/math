(** Federer (1969), 3.2.20, pp. 256–257: the
    area formula for a measurable finite-mass rectifiable set and
    a Lipschitz map on its exact original partial domain. Both
    integrands retain the printed extended-real weight. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  PartialFunctionExtensionUP PartialZeroExtension MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality
  MeasurableZeroExtension MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralAlmostEquality
  HausdorffMeasure RectifiableSetUP LipschitzUP LipschitzBasic PartialMetricLipschitz EuclideanPartialLipschitzExtension
  RectifiableCompactChartsUP RectifiableCompactCharts RectifiableDensityDifferentiability
  MeasureApproximateJacobian NonnegativePartialRealExtension TotalScalarCutoff
  ZeroExtendedDensityWeightAgreement PartialAreaWeightExtension PartialMappingMultiplicity MappingMultiplicity
  RectifiableAreaIntegrands RectifiableAreaDecomposition CountableAreaTransformation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_area_global_extension]: complete compact-chart
    proof of Federer 3.2.20, p. 257, for a global Lipschitz
    extension restricted back to W. It works in all ambient dimensions;
    the numbered wrapper below retains the printed m<=v hypothesis.
    The intrinsic Jacobian remains partial at exceptional points and
    no auxiliary density or decomposition is a final hypothesis. *)
Theorem rectifiable_area_global_extension (R : realType) m n k
    (W : set (R_n R n)) (F : R_n R n -> R_n R k) :
  is_measure_m_rectifiable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R k)) setT F ->
  forall (g : R_n R k -> \bar R) a,
    is_measure_integral (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
      (rectifiable_area_source_integrand m W (partial_function_source_restrict W (partial_function_total F)) g) a <->
    is_measure_integral (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R k)) m)
      (rectifiable_area_target_integrand (partial_function_source_restrict W (partial_function_total F)) g) a.
Proof.
move=> hRect hW hF g a.
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose Z := inner_metric_space (@euclidean_inner_productP R k).
pose beta := @hausdorff_measure R Y m.
pose gamma := @hausdorff_measure R Z m.
have hb := @hausdorff_measure_is_measure R Y m.
have hg := @hausdorff_measure_is_measure R Z m.
have hr := measure_restrict_is_measure hb W.
pose f0 := partial_function_source_restrict W (partial_function_total F).
pose d := measure_approximate_jacobian (measure_restrict beta W) m m f0.
have hPos w j : partial_function_graph d w j -> (0<=j)%R.
  exact: (@measure_approximate_jacobian_nonnegative R n k (measure_restrict beta W) m m f0 w j).
have [J [hJPos hJExt]] := @nonnegative_partial_real_extension R Y d hPos.
have hTwo : (1<(2:R))%R by rewrite ltr1n.
have [K [psi hCover]] := @federer_3_2_18 R m n 2%R W hRect hW hTwo.
have hDecomp := @rectifiable_area_chart_decomposition R m n k 2%R W K psi F J
  hTwo hCover hW hRect.2 hF hJPos hJExt.
pose p := total_scalar_cutoff W J.
have hTransform := @countable_area_decomposition_transform R Y Z Z beta gamma hb hg
  F (fun z=>z) p (fun i=>total_scalar_cutoff (psi i @` K i) J)
  (fun z=>@mapping_multiplicity R Y Z F W z)
  (fun i z=>@mapping_multiplicity R Y Z F (psi i @` K i) z) hDecomp.
have hFull := rectifiable_density_and_differentiability_global hRect hW hF.
have hDomain : measure_almost_everywhere_on beta W (partial_function_domain d).
  apply: (measure_null_subset hb _ hFull)=> w [hw hn].
  split; first exact hw.
  move=> [_ [_ hApprox]]; apply: hn.
  rewrite /d (@measure_approximate_jacobian_domain R n k (measure_restrict beta W) m m f0 hr).
  exact hApprox.
have hDomainZero := (@zero_extension_relative_domain R Y (real_line_metric R) beta 0%R W d).1 hDomain.
have hCutExt : is_partial_function_total_extension
    (partial_function_zero_extension (0%R:real_line_metric R) W d) p.
  move=> w j hj; change (total_scalar_cutoff W J w=j).
  case: (pselect (W w))=> hw.
  - rewrite (total_scalar_cutoff_on J hw).
    have hJ := (partial_function_zero_extension_on _ _ _ hw).1 hj.
    exact: (hJExt w j hJ).
  - have hj0 := (partial_function_zero_extension_off _ _ _ hw).1 hj.
    by rewrite (total_scalar_cutoff_off J hw) hj0.
have hDensity := @zero_extended_density_weight_agreement R Y beta hb W d p
  (fun w=>(g (F w):extended_real_line R)) hDomainZero hCutExt.
pose de := extended_measure_approximate_jacobian (measure_restrict beta W) m m f0.
have hWeightGraph := @restricted_partial_area_weight_graph R Y Z W F g de.
have hSource : measure_almost_equal beta (rectifiable_area_source_integrand m W f0 g)
    (partial_function_total (fun w=>g (F w)* (p w)%:E : extended_real_line R)).
  apply: (@measure_almost_everywhere_mono R Y beta hb _ _ _ hDensity)=> w [t [hOld hP]].
  exists t; split; last exact hP.
  exact: (hWeightGraph w t).2 hOld.
have hDomF0 : partial_function_domain f0=W.
  by rewrite /f0 partial_function_source_restrict_domain partial_function_total_domain setIT.
have hF0Ext : is_partial_function_total_extension f0 F.
  by move=> w y [hw hy].
have hMultiplicity z := @partial_mapping_multiplicity_total_extension R Y Z f0 F z hF0Ext.
rewrite hDomF0 in hMultiplicity.
have hTarget z t : partial_function_graph
    (partial_function_total (fun z=>g z* @mapping_multiplicity R Y Z F W z : extended_real_line R)) z t <->
    partial_function_graph (rectifiable_area_target_integrand f0 g) z t.
  change (g z* @mapping_multiplicity R Y Z F W z=t <->
    g z* @partial_mapping_multiplicity R Y Z f0 z=t).
  by rewrite hMultiplicity.
split=> hI.
- have hIP := measure_integral_almost_equal hb hI hSource.
  exact: (measure_integral_graph_equivalent hTarget ((hTransform g a).1 hIP)).
- have hIT := measure_integral_graph_equivalent (fun z t=>iff_sym (hTarget z t)) hI.
  have hIP := (hTransform g a).2 hIT.
  exact: (measure_integral_almost_equal hb hIP (MeasureAlmostEquality.measure_almost_equal_sym hSource)).
Qed.

(** Source for [federer_3_2_20]: the whole area transformation in
    Federer 3.2.20, pp. 256–257. W is measurable and
    (H^m,m) rectifiable, f has exactly domain W and is Lipschitz,
    and m is at most the target dimension. For every extended-real
    g the two integral value graphs agree, including both infinities
    and the case in which neither signed integral is defined. *)
Theorem federer_3_2_20 (R : realType) m n k
    (W : set (R_n R n)) (f : partial_function (R_n R n) (R_n R k)) :
  (m<=k)%N ->
  is_measure_m_rectifiable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  partial_function_domain f=W ->
  (exists L,@is_partial_metric_lipschitz_bound R (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R k)) f L) ->
  forall (g : R_n R k -> \bar R) a,
    is_measure_integral (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
      (rectifiable_area_source_integrand m W f g) a <->
    is_measure_integral (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R k)) m)
      (rectifiable_area_target_integrand f g) a.
Proof.
move=> hmk hRect hW hDom [L hLip].
have [F [hF hGraph]] := euclidean_partial_lipschitz_global_extension hLip.
rewrite hDom in hGraph.
rewrite hGraph.
exact: (rectifiable_area_global_extension hRect hW (metric_lipschitz_of_bound hF)).
Qed.
