(** Federer (1969), 3.2.22, p. 258:
    independent laws for all three conclusions of
    rectifiable coarea on the original partial domain. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPostcomposition PartialMetricLipschitz
  MeasureUP MeasureAlmostUP MeasureRestriction MeasureIntegralUP MeasureSubsetIntegral HausdorffMeasure
  MeasureApproximateDifferentialUP MeasureApproximateTangentUP PartialExteriorNormUP RectifiableTangentPlaneUP
  RectifiableSetUP PartialMappingMultiplicity RectifiableCoareaIntegrands.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_rectifiable_coarea]: all three
    conclusions of Federer 3.2.22, p. 258.
    These are independent mathematical laws to prove,
    not new axioms, selected differential fields or
    a construction of the original map and measures. *)
Record is_rectifiable_coarea (R:realType) m n mu v
    (W:set (R_n R n)) (Z:set (R_n R v))
    (f:partial_function (R_n R n) (R_n R v)):Prop:={
  (** Source for [rectifiable_coarea_image_law]: exact
      intrinsic-Jacobian-zero or target tangent-image
      alternative, Federer 3.2.22(1), p. 258. *)
  rectifiable_coarea_image_law : measure_almost_everywhere_on (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W [set w|
      exists (z:R_n R v) (d:partial_function (R_n R n) (R_n R v)) (j:R),
        partial_function_graph f w z /\
        is_measure_approximate_differential (inner_norm (@euclidean_inner_productP R v))
          (inner_norm_real_norm (@euclidean_inner_productP R n))
          (measure_restrict (@hausdorff_measure R
            (inner_metric_space (@euclidean_inner_productP R n)) m) W) m f w d /\
        is_partial_exterior_norm mu d j /\
        (j=0%R \/ (partial_function_range d=
          measure_approximate_tangent_cone (inner_norm_real_norm (@euclidean_inner_productP R v))
            (measure_restrict (@hausdorff_measure R
              (inner_metric_space (@euclidean_inner_productP R v)) mu) Z) mu z /\
          is_m_dimensional_approximate_tangent mu
            (measure_restrict (@hausdorff_measure R
              (inner_metric_space (@euclidean_inner_productP R v)) mu) Z) z))];
  (** Source for [rectifiable_coarea_fibre_law]: finite-mass
      rectifiable and measurable actual fibres almost
      everywhere, Federer 3.2.22(2), p. 258. *)
  rectifiable_coarea_fibre_law : measure_almost_everywhere_on (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) Z [set z|
      is_measure_m_rectifiable (@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) (m-mu)) (m-mu) (partial_mapping_fibre f z) /\
      measure_measurable (@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) (m-mu)) (partial_mapping_fibre f z)];
  (** Source for [rectifiable_coarea_integral_law]: every
      extended-real integrable weight on its exact original
      domain satisfies the actual weighted identity,
      Federer 3.2.22(3), p. 258. *)
  rectifiable_coarea_integral_law : forall g:partial_function (R_n R n) (extended_real_line R),
    partial_function_domain g=W ->
    is_measure_integrable (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) W) g ->
    exists a,is_measure_integral (@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) m)
        (rectifiable_coarea_source_integrand m mu W f g) a /\
      is_measure_subset_integral (@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R v)) mu) Z
        (rectifiable_coarea_fibre_integral m mu f g) a
}.
