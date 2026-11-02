(** Federer (1969), 2.10.45, printed pp. 202–203: Hausdorff measure of
    products with a Euclidean factor, with the printed coefficient bounds.
    Here k and m are natural degrees; the common Gamma-normalised
    real-degree extension remains separately pending. No relevant entry
    occurs in the working Federer erratum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric SquaredMetricProductUP
  EuclideanBallVolume EuclideanLebesgue EuclideanLebesgueDimensions HausdorffMeasure MetricProductRectangles
  HausdorffProductSliceMeasure HausdorffEuclideanProduct EuclideanProductCoefficientNormalisation MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_2_10_45]: direct natural-degree
    theorem of 2.10.45, pp. 202–203, with the
    exact squared product metric and both printed bounds.
    Every Lebesgue-measurable U is admitted, including
    infinite measure, and V need not be measurable.
    Empty and zero-mass factors and either zero degree
    are included. Write the half-power as a power
    of the nonnegative square root. *)
Theorem federer_2_10_45 (R : realType) m k (P Y : metricType R)
    (pair : inner_metric_space (@euclidean_inner_productP R m) -> Y -> P)
    first second (hp : is_squared_metric_product pair first second) (V : set Y) :
  (hausdorff_measure k V< +oo)%E -> exists c : R,
    (euclidean_unit_ball_volume R m)^-1<=
      c*euclidean_unit_ball_volume R k/euclidean_unit_ball_volume R (k+m) /\
    c*euclidean_unit_ball_volume R k/euclidean_unit_ball_volume R (k+m)<=
      (Num.sqrt m.+1%:R)^+(k+m)/(2:R)^+m /\
    forall U, measure_measurable (@euclidean_lebesgue_measure R m) U ->
      hausdorff_measure (k+m) (metric_product_rectangle first second U V)=
        (c%:E*euclidean_lebesgue_measure m U*hausdorff_measure k V)%E.
Proof.
move=> hV; have [c [hl [hu he]]] :=
  @hausdorff_euclidean_product_coefficient R m k P Y pair first second hp V hV.
have [hnl hnu] := euclidean_product_coefficient_normalisation hl hu.
exists c; split=> //; split=> // U hU; exact: he U hU.
Qed.
