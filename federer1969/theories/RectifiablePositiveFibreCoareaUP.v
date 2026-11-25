(** Federer (1969), 3.2.32, p. 269: independent
    laws for the two conclusions on the exact positive-fibre
    locus of the original Lipschitz partial map. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  PartialFunctionUP PartialFunctionBasic MeasureRestriction HausdorffMeasure MeasureApproximateDifferentialUP
  PartialImageDimensionUP MeasureApproximateJacobian MeasureIntegralUP MeasureSubsetIntegral ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_partial_fibre_locus]: the set Y in
    Federer 3.2.32, p. 269. A target point belongs
    exactly when its original partial fibre has positive
    complementary-dimensional Hausdorff mass, possibly infinite. *)
Definition positive_partial_fibre_locus (R:realType) n v m mu
    (f:partial_function (R_n R n) (R_n R v)):set (R_n R v):=
  [set y|0<@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n))
    (m-mu) (partial_function_preimage f [set y])].

(** Source for [partial_approximate_image_dimension_locus]: the
    set X in Federer 3.2.32, p. 269. The actual
    partial approximate differential relative to the original
    source exists and its exact image has dimension at most mu.
    The condition is <=mu, including the zero-Jacobian branch. *)
Definition partial_approximate_image_dimension_locus (R:realType) n v m mu
    (f:partial_function (R_n R n) (R_n R v)):set (R_n R n):=
  partial_function_domain f `&` [set x|exists d,
    is_measure_approximate_differential (inner_norm (@euclidean_inner_productP R v))
      (inner_norm_real_norm (@euclidean_inner_productP R n))
      (measure_restrict (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
        (partial_function_domain f)) m f x d /\is_partial_image_dimension_at_most mu d].

(** Source for [is_rectifiable_positive_fibre_coarea]: both
    conclusions of Federer 3.2.32, p. 269. These
    laws specify the null rank exception and an actual common
    source/target integral value. They postulate no theorem,
    chosen differential field, measurability of a source preimage,
    finite individual fibre mass or finite integral value. *)
Record is_rectifiable_positive_fibre_coarea (R:realType) n v m mu
    (f:partial_function (R_n R n) (R_n R v)):Prop:={
  (** Source for [rectifiable_positive_fibre_rank_law]: the first
      conclusion H^m(f^-1(Y) minus X)=0 in Federer 3.2.32, p. 269. *)
  rectifiable_positive_fibre_rank_law:@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m
    (partial_function_preimage f (positive_partial_fibre_locus m mu f) `\`
      partial_approximate_image_dimension_locus m mu f)=0;
  (** Source for [rectifiable_positive_fibre_integral_law]: the
      displayed integral identity in Federer 3.2.32, p. 269.
      The public approximate Jacobian retains its exact partial domain. *)
  rectifiable_positive_fibre_integral_law:exists a,
    is_measure_subset_integral (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m)
      (partial_function_preimage f (positive_partial_fibre_locus m mu f))
      (extended_measure_approximate_jacobian (measure_restrict (@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) m) (partial_function_domain f)) m mu f) a /\
    is_measure_integral (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R v)) mu)
      (partial_function_total (fun y=>(@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) (m-mu)
        (partial_function_preimage f [set y]):extended_real_line R))) a
}.
