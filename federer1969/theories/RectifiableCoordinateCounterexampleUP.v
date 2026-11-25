(** Federer (1969), 3.2.27, pp. 262–263: independent
    laws of the local counterexample to the unrestricted
    upper inequality. This correction is absent from the
    working erratum. Actual coordinate integrals, finite
    rectifiability and source nonmeasurability remain separate. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric ExteriorIndices
  SingleCoordinateProjection RectifiableSetUP RectifiableCoordinateMassUP HausdorffMeasure MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_rectifiable_coordinate_counterexample]: independent
    specifications for the local two-sheet correction to
    3.2.27, pp. 262–263. The actual horizontal
    and vertical masses are one and zero, whereas the
    finite rectifiable source has outer length greater
    than one. Existence is proved separately. *)
Record is_rectifiable_coordinate_counterexample (R:realType)
    (W:set (R_n R 2)) (a:Lambda 2 1->R):Prop:={
  (** Source for [coordinate_counterexample_rectifiable]: genuine
      one-rectifiability of the local example testing
      3.2.27, pp. 262–263, by 3.2.14, p. 251. *)
  coordinate_counterexample_rectifiable:
    @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R 2)) 1 W;
  (** Source for [coordinate_counterexample_finite_rectifiable]: finite
      (H^1,1) rectifiability required by the printed
      hypothesis of 3.2.27, p. 262. *)
  coordinate_counterexample_finite_rectifiable:
    is_measure_m_rectifiable (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R 2)) 1) 1 W;
  (** Source for [coordinate_counterexample_integrals]: the actual
      coordinate fibre-count integral definition in
      3.2.27, p. 262, satisfied by the local example. *)
  coordinate_counterexample_integrals:is_rectifiable_coordinate_masses W a;
  (** Source for [coordinate_counterexample_values]: the two actual
      coordinate integral values in the local example
      correcting the unrestricted upper inequality of
      3.2.27, pp. 262–263. *)
  coordinate_counterexample_values:
    a (single_coordinate_selection (ord0:'I_2))= 1%R /\
    a (single_coordinate_selection (ord_max:'I_2))=0%R;
  (** Source for [coordinate_counterexample_sum]: coordinate-mass sum
      one in the local test of the upper inequality
      in 3.2.27, pp. 262–263. *)
  coordinate_counterexample_sum:(\sum_lambda a lambda)%R= 1%R;
  (** Source for [coordinate_counterexample_excess]: strict failure
      of the printed upper bound in 3.2.27, p. 262.
      The source outer length exceeds one. *)
  coordinate_counterexample_excess:
    1<@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2)) 1 W;
  (** Source for [coordinate_counterexample_nonmeasurable]: necessity
      of the source-measurability correction to 3.2.27,
      pp. 262–263, verified on the local two-sheet example. *)
  coordinate_counterexample_nonmeasurable:
    ~measure_measurable (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R 2)) 1) W
}.
