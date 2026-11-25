(** Federer (1969), 3.2.33, p. 270: independent
    laws of the complete smooth counterexample, using exactly
    the original-domain objects of 3.2.32. Existence is separate. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  NormRegularity PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialMetricLipschitz
  MeasureUP MeasureRestriction HausdorffMeasure MeasureApproximateJacobian MeasureSubsetIntegral
  RectifiableSetUP RectifiablePositiveFibreCoareaUP EuclideanOpenUnitCube.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Example.
Variable R:realType.
Variables mu m:nat.
Variable F:R_n R m->R_n R (mu+1).
Local Notation W:=(@euclidean_open_unit_cube R m).
Local Notation H:=(@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) m).
Local Notation f:=(partial_function_source_restrict W (partial_function_total F)).
Local Notation X:=(partial_approximate_image_dimension_locus m mu f).
Local Notation Y:=(positive_partial_fibre_locus m mu f).

(** Source for [is_smooth_coarea_remainder_example]: the smooth
    example of Federer 3.2.33, p. 270. The independent
    specification retains every hypothesis of 3.2.32, actual
    class infinity on W, its original low-rank locus X,
    empty positive-fibre set Y and a strictly positive actual
    remainder integral. No theorem or example is assumed to
    exist, and no selected differential field is supplied. *)
Record is_smooth_coarea_remainder_example:Prop:={
  (** Source for [smooth_remainder_example_class]: f has class
      infinity, Federer 3.2.33, p. 270. *)
  smooth_remainder_example_class:norm_class_all_orders
    (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R (mu+1))) W F;
  (** Source for [smooth_remainder_example_rectifiable]: the finite
      rectifiable-source premise of 3.2.32 holds, as required
      by 3.2.33, p. 270. *)
  smooth_remainder_example_rectifiable:is_measure_m_rectifiable H m W;
  (** Source for [smooth_remainder_example_measurable]: the original
      source W is H^m measurable, Federer 3.2.33, p. 270. *)
  smooth_remainder_example_measurable:measure_measurable H W;
  (** Source for [smooth_remainder_example_lipschitz]: f has a
      finite Lipschitz bound on its exact domain,
      Federer 3.2.33, p. 270. *)
  smooth_remainder_example_lipschitz:exists L,
    @is_partial_metric_lipschitz_bound R (inner_metric_space (@euclidean_inner_productP R m))
      (inner_metric_space (@euclidean_inner_productP R (mu+1))) f L;
  (** Source for [smooth_remainder_example_coarea]: both assertions
      of 3.2.32 actually hold for the example in 3.2.33,
      p. 270; they do not eliminate the omitted integral. *)
  smooth_remainder_example_coarea:is_rectifiable_positive_fibre_coarea m mu f;
  (** Source for [smooth_remainder_example_empty_fibres]: Y is empty,
      Federer 3.2.33, p. 270, because every required fibre mass is zero. *)
  smooth_remainder_example_empty_fibres:Y=set0;
  (** Source for [smooth_remainder_example_positive_source]: the exact
      low-rank locus X has positive H^m mass,
      Federer 3.2.33, p. 270. *)
  smooth_remainder_example_positive_source:(0<H X)%E;
  (** Source for [smooth_remainder_example_integral]: the actual
      integral over X minus f^-1(Y) equals H^m(X)>0,
      strengthening the printed lower bound in 3.2.33, p. 270. *)
  smooth_remainder_example_integral:is_measure_subset_integral H
    (X `\` partial_function_preimage f Y)
    (extended_measure_approximate_jacobian (measure_restrict H (partial_function_domain f)) m mu f)
    (H X)
}.
End Example.
