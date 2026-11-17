(** Federer 2.10.45, pp. 202-203: the complete original product
    theorem with a Euclidean factor and arbitrary real section degree.
    Keep the finite-measure condition on V and arbitrary measurable U. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric SquaredMetricProductUP
  EuclideanBallVolume EuclideanLebesgueDimensions MetricProductRectangles
  RealHausdorffMeasure RealHausdorffNormalisation RealHausdorffBallCoefficient RealPower
  RealHausdorffProductSliceMeasure RealHausdorffEuclideanProduct
  RealEuclideanProductCoefficientNormalisation MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_2_10_45_real]: direct theorem and both
    printed coefficient bounds of Federer 2.10.45, pp. 202-203.
    Use every real k>=0, the actual Gamma normalization and the exact
    squared product metric. V need not be measurable; U may have infinite
    Lebesgue measure. Retain zero mass and either zero degree. *)
Theorem federer_2_10_45_real (R : realType) (m : nat) (k : R)
    (hk : 0 <= k) (P Y : metricType R)
    (pair : inner_metric_space (@euclidean_inner_productP R m) -> Y -> P)
    first second (hp : is_squared_metric_product pair first second) (V : set Y) :
  (@real_hausdorff_measure R Y k hk V < +oo)%E -> exists c : R,
    (euclidean_unit_ball_volume R m)^-1 <=
      c*real_hausdorff_ball_coefficient hk/
        real_hausdorff_ball_coefficient (addr_ge0 hk (ler0n R m)) /\
    c*real_hausdorff_ball_coefficient hk/
        real_hausdorff_ball_coefficient (addr_ge0 hk (ler0n R m)) <=
      real_power (Num.sqrt m.+1%:R) (k+m%:R)/(2:R)^+m /\
    forall U, measure_measurable (@euclidean_lebesgue_measure R m) U ->
      @real_hausdorff_measure R P (k+m%:R)%R (addr_ge0 hk (ler0n R m))
        (metric_product_rectangle first second U V) =
      (c%:E*euclidean_lebesgue_measure m U* @real_hausdorff_measure R Y k hk V)%E.
Proof.
move=> hV.
have [c [hl [hu he]]] := @real_hausdorff_euclidean_product_coefficient R m k hk
  P Y pair first second hp V hV.
have [hnl hnu] := real_euclidean_product_coefficient_normalisation hl hu.
exists c; split=> //; split=> // U hU; exact: he U hU.
Qed.
