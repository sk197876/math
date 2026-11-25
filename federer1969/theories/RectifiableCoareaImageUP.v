(** Federer (1969), 3.2.22(1), p. 258: abstract
    laws for the approximate-differential image alternative.
    The original source domain W and both restricted
    Hausdorff measures remain explicit. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialMetricLipschitz
  MeasureRestriction HausdorffMeasure MeasureApproximateDifferentialUP MeasureApproximateTangentUP
  PartialExteriorNormUP RectifiableTangentPlaneUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_rectifiable_coarea_image_point]: the
    precise pointwise alternative in Federer 3.2.22(1),
    p. 258. An actual partial approximate differential
    and its actual intrinsic mu-Jacobian exist; either
    that Jacobian is zero or its exact image is
    the mu-dimensional approximate tangent vector space
    of Z. This predicate specifies laws, not a
    selected differential, norm witness or new axiom. *)
Definition is_rectifiable_coarea_image_point (R:realType) m n mu v
    (W:set (R_n R n)) (Z:set (R_n R v)) (F:R_n R n->R_n R v) w:Prop:=
  exists (d:partial_function (R_n R n) (R_n R v)) (j:R),
    is_measure_approximate_differential (inner_norm (@euclidean_inner_productP R v))
      (inner_norm_real_norm (@euclidean_inner_productP R n))
      (measure_restrict (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W)
      m (partial_function_source_restrict W (partial_function_total F)) w d /\
    is_partial_exterior_norm mu d j /\
    (j=0 \/ (partial_function_range d=
      measure_approximate_tangent_cone (inner_norm_real_norm (@euclidean_inner_productP R v))
        (measure_restrict (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R v)) mu) Z)
        mu (F w) /\
      is_m_dimensional_approximate_tangent mu
        (measure_restrict (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R v)) mu) Z)
        (F w))).
