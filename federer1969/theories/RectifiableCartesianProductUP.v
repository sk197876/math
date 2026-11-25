(** Federer (1969), 3.2.23, p. 260: independent laws for
    the rectifiability and exact restricted measure of a Cartesian
    product. The usual Euclidean block identification is explicit;
    the laws make no reference to a parametrization or construction. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanCartesianMap RectifiableSetUP HausdorffMeasure
  MeasureUP MeasureRestriction MeasurePushforward ProductMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_rectifiable_cartesian_product]: the two
    conclusions of Federer 3.2.23, p. 260, as a predicate
    of proved mathematical laws. In particular the measure equality
    is the equality of entire outer measures, not just a formula
    for the total mass of W times Z. *)
Record is_rectifiable_cartesian_product (R:realType) (m mu n v:nat)
    (W:set (R_n R n)) (Z:set (R_n R v)):Prop:={
  (** Source for [rectifiable_cartesian_rectifiability_law]: the
      (H^(m+mu),m+mu)-rectifiability conclusion of Federer 3.2.23,
      p. 260, including finite mass in the convention of 3.2.14. *)
  rectifiable_cartesian_rectifiability_law:
    is_measure_m_rectifiable (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R (n+v))) (m+mu))
      (m+mu) (euclidean_cartesian_set W Z);
  (** Source for [rectifiable_cartesian_measure_law]: the displayed
      equality H^(m+mu) restricted to W times Z equals the Cartesian
      product of H^m restricted to W and H^mu restricted to Z,
      Federer 3.2.23, p. 260. The usual block split of 2.6.5,
      p. 120, identifies the two ambient carriers. *)
  rectifiable_cartesian_measure_law:
    measure_pushforward (@euclidean_block_split R n v)
      (measure_restrict (@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R (n+v))) (m+mu))
        (euclidean_cartesian_set W Z))=
    product_measure
      (measure_restrict_is_measure (@hausdorff_measure_is_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) m) W)
      (measure_restrict_is_measure (@hausdorff_measure_is_measure R
        (inner_metric_space (@euclidean_inner_productP R v)) mu) Z)
}.
