(** Federer (1969), 3.2.32, pp. 269–270: the
    approximate differential has image dimension at most mu on
    a finite rectifiable source mapping into a finite rectifiable
    target. Both alternatives of 3.2.22(1) are used. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  LipschitzUP PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialMetricLipschitz
  PartialLinearChartGraph MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureRestriction HausdorffMeasure
  MeasureApproximateDifferentialUP MeasureApproximateDifferentialUniqueness MeasureApproximateJacobianChart
  RectifiableSetUP RectifiableCoareaImageUP RectifiableCoareaImage RectifiableTangentPlaneUP
  RectifiableDifferentialChartUP RectifiableDifferentialChartSupply
  PartialImageDimensionUP PartialExteriorZeroImageDimension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_coarea_image_dimension_almost]: supporting
    the exceptional-set assertion of Federer 3.2.32, p. 269,
    using 3.2.22(1), p. 258. In the nonzero Jacobian
    branch the image is the actual mu-dimensional target tangent.
    In the zero branch actual injective source-chart coordinates
    and the vanishing exterior norm prove smaller image dimension.
    No supplied rank, chart or differential field is assumed. *)
Theorem rectifiable_coarea_image_dimension_almost (R:realType) m n mu v
    (W:set (R_n R n)) (Z:set (R_n R v)) (F:R_n R n->R_n R v):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) mu Z ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) Z ->
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R v)) setT F ->
  (forall w,W w ->Z (F w)) ->
  measure_almost_everywhere_on (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W [set w|
      exists d,is_measure_approximate_differential (inner_norm (@euclidean_inner_productP R v))
        (inner_norm_real_norm (@euclidean_inner_productP R n))
        (measure_restrict (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W)
        m (partial_function_source_restrict W (partial_function_total F)) w d /\
        is_partial_image_dimension_at_most mu d].
Proof.
move=>hRectW hW hRectZ hZ hF hRange.
have hH:=@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.
have hImage:=@rectifiable_coarea_image_almost R m n mu v W Z F hRectW hW hRectZ hZ hF hRange.
have hChart:=@rectifiable_differential_chart_supply_almost R m n v W F hRectW hW hF.
have hBoth:=measure_almost_everywhere_and hH
  ((measure_almost_everywhere_on_implication _ _ _).1 hImage)
  ((measure_almost_everywhere_on_implication _ _ _).1 hChart).
apply:(measure_almost_everywhere_on_implication _ _ _).2.
apply:(measure_almost_everywhere_mono hH _ hBoth)=>w [hI hC] hw.
have [d [j [hD [hNorm hAlternative]]]]:=hI hw.
exists d; split; first exact hD.
case:hAlternative=>[hj|[hRangeD [P hPlane]]].
- have [K [psi [a [D [A [d0 [ha [hpsi [hInj [hDa [hAa [hCone [hD0 hComp]]]]]]]]]]]]]:=hC hw.
  have hEqual:d0=d:=measure_approximate_differential_unique hD0 hD.
  rewrite hEqual in hComp.
  have hDom:=measure_approximate_differential_specification_domain hD.
  rewrite hCone in hDom.
  have hGraph:=partial_linear_chart_graph hDom hComp.
  rewrite hj in hNorm.
  exact (@zero_partial_exterior_chart_image_dimension R m n v mu D A d hInj hGraph hNorm).
- exists mu,P; split; first exact:leqnn.
  exact:(eq_trans hRangeD hPlane).
Qed.
