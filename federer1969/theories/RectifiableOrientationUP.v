(** Federer (1969), 3.2.25, p. 261: specify a measurable
    orientation by its mathematical laws, independently of compact
    charts or any selected tangent-frame construction. The erratum
    p. 5, book p. 261 line 4, retains H^m almost everywhere. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness EuclideanLinearMaps InnerExteriorPositivity ExteriorGrading ExteriorNorm AssociatedSubspace
  PartialFunctionUP MeasureRestriction MeasureAlmostUP MeasurableFunctionUP HausdorffMeasure
  MeasureApproximateTangentUP RectifiableTangentPlaneUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_rectifiable_measurable_orientation]: all
    conclusions of Federer 3.2.25, p. 261: measurability
    under H^m restricted to W, simple unit values at every
    defined point, and the exact associated m-dimensional
    approximate tangent plane almost everywhere on W. *)
Record is_rectifiable_measurable_orientation (R:realType) m n
    (W:set (R_n R n)) (T:partial_function (R_n R n) (exterior_power (R_n R n) m)):Prop:={
  (** Source for [rectifiable_orientation_measurable]: the
      H^m restricted-to-W measurability clause of 3.2.25,
      p. 261, in the partial-domain convention of 2.3.2. *)
  rectifiable_orientation_measurable:
    @is_measure_measurable_function R
      [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
      [the topologicalType of inner_metric_space (@exterior_inner_productP R
        (euclidean_two_nonzero R) (R_n R n) (@euclidean_inner_product R n)
        (@euclidean_inner_productP R n) m)]
      (measure_restrict (@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) m) W) T;
  (** Source for [rectifiable_orientation_unit_simple]: the
      displayed simple unit m-vector range in 3.2.25,
      p. 261. Every value satisfies these laws, including
      exceptional defined points, rather than only almost everywhere. *)
  rectifiable_orientation_unit_simple:forall w xi,partial_function_graph T w xi ->
    simple xi /\ @exterior_norm R (euclidean_two_nonzero R) (R_n R n)
      (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m xi= 1;
  (** Source for [rectifiable_orientation_tangent]: the actual
      approximate tangent equals the associated m-dimensional
      vector subspace, H^m almost everywhere on W, in
      3.2.25, p. 261, with erratum p. 5 line 4. *)
  rectifiable_orientation_tangent:
    measure_almost_everywhere_on (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) W [set w|
      exists xi,partial_function_graph T w xi /\
        measure_approximate_tangent_cone (inner_norm_real_norm (@euclidean_inner_productP R n))
          (measure_restrict (@hausdorff_measure R
            (inner_metric_space (@euclidean_inner_productP R n)) m) W) m w=
          [set v|FedererSimple.T xi v] /\
        is_m_dimensional_approximate_tangent m
          (measure_restrict (@hausdorff_measure R
            (inner_metric_space (@euclidean_inner_productP R n)) m) W) w]
}.
