(** Federer (1969), 3.2.22(1), p. 258:
    the image alternative for the actual partial map f. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  LipschitzUP LipschitzBasic PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialMetricLipschitz
  EuclideanPartialLipschitzExtension MeasureRestriction HausdorffMeasure MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureApproximateDifferentialUP MeasureApproximateTangentUP PartialExteriorNormUP RectifiableTangentPlaneUP
  RectifiableSetUP RectifiableCoareaImageUP RectifiableCoareaImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [federer_3_2_22_1]: the complete
    assertion (1) of Federer 3.2.22, p. 258.
    At H^m almost every w of W the actual
    approximate differential and intrinsic mu-Jacobian exist;
    either the Jacobian is zero or the differential's
    exact image is the mu-dimensional approximate tangent
    vector space of Z at the actual value f(w).
    The global extension is only auxiliary. No values
    outside the original domain or exceptional undefined
    approximate-Jacobian domain enter this statement. *)
Theorem federer_3_2_22_1 (R:realType) m n mu v
    (W:set (R_n R n)) (Z:set (R_n R v))
    (f:partial_function (R_n R n) (R_n R v)):
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
  partial_function_range f `<=` Z ->
  measure_almost_everywhere_on (@hausdorff_measure R
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
              (inner_metric_space (@euclidean_inner_productP R v)) mu) Z) z))].
Proof.
move=>hDim hRectW hW hRectZ hZ hDomain [L hLip] hRange.
have [F [hBound hEq]]:=euclidean_partial_lipschitz_global_extension hLip.
rewrite hDomain in hEq.
have hGraph:forall w,W w ->partial_function_graph f w (F w).
  move=>w hw; rewrite hEq; by split.
have hImage:forall w,W w ->Z (F w).
  move=>w hw; apply:hRange; exists w; exact:(hGraph w hw).
have hCore:=rectifiable_coarea_image_almost hRectW hW hRectZ hZ
  (metric_lipschitz_of_bound hBound) hImage.
have hr:=@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.
apply:(measure_almost_everywhere_on_implication _ _ _).2.
apply:(measure_almost_everywhere_mono hr _
  ((measure_almost_everywhere_on_implication _ _ _).1 hCore))=>w hPoint hw.
have [d [j [hApx [hNorm hAlternative]]]]:=hPoint hw.
exists (F w),d,j; split; first exact:(hGraph w hw).
rewrite hEq; by split; last split.
Qed.
