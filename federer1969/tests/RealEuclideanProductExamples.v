(** Project endpoint regressions for Federer 2.10.45, pp. 202-203.
    Check the exact coefficient at Euclidean dimension zero and the
    finite null second factor in nonintegral degree. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates EuclideanSquaredProduct
  SquaredMetricProductUP EuclideanBallVolume EuclideanLebesgueDimensions
  RealHausdorffMeasure RealHausdorffNormalisation RealHausdorffBallCoefficient
  EulerGammaHalfParameters RealPower RealHausdorffEuclideanProductTheorem
  MetricProductRectangles MeasureUP MeasureBasic MeasureSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_product_zero_euclidean_dimension]: project
    regression for Federer 2.10.45, pp. 202-203. The actual product
    of R^0 with any metric space is that space. The theorem's two
    original bounds force its coefficient to be exactly one, at every
    real section degree, even when the prescribed factor is null. *)
Theorem real_product_zero_euclidean_dimension (R : realType)
    (Y : metricType R) (k : R) (hk : 0 <= k) (V : set Y) :
  (@real_hausdorff_measure R Y k hk V < +oo)%E ->
  exists c : R, c = 1 /\ forall U,
    measure_measurable (@euclidean_lebesgue_measure R 0) U ->
    @real_hausdorff_measure R Y (k+0%:R)%R (addr_ge0 hk (ler0n R 0))
      (metric_product_rectangle
        (fun _ : Y => (0 : inner_metric_space (@euclidean_inner_productP R 0))) id U V) =
    (c%:E*euclidean_lebesgue_measure 0 U* @real_hausdorff_measure R Y k hk V)%E.
Proof.
move=> hV.
pose E := inner_metric_space (@euclidean_inner_productP R 0).
pose pair := fun (_ : E) (y : Y) => y.
pose first := fun _ : Y => (0 : E).
have hp : is_squared_metric_product pair first id.
  constructor.
  - move=> x y; exact: esym (@coordinate_zero R x).
  - by move=> x y.
  - by move=> y.
  - move=> x y u v.
    have he : x = u by rewrite (@coordinate_zero R x) (@coordinate_zero R u).
    by rewrite he mdistxx expr0n add0r.
have [c [hl [hu he]]] := @federer_2_10_45_real R 0%N k hk Y Y
  pair first id hp V hV.
have hAlpha (p : R) (hq : 0 <= p) : p = k ->
    real_hausdorff_ball_coefficient hq = real_hausdorff_ball_coefficient hk.
  move=> h; subst p.
  by rewrite /real_hausdorff_ball_coefficient
    (euler_gamma_proof_irrelevant (real_dimension_gamma_parameter hq)
      (real_dimension_gamma_parameter hk)).
have ha := hAlpha (k+0%:R)%R (addr_ge0 hk (ler0n R 0)) (addr0 k).
have hnonzero : real_hausdorff_ball_coefficient hk != 0.
  exact: lt0r_neq0 (real_hausdorff_ball_coefficient_positive hk).
rewrite ha mulfK // in hl hu.
rewrite euclidean_unit_ball_volume0 invr1 in hl.
rewrite /= sqrtr1 real_power_one_base expr0 divr1 in hu.
have hc : c = 1 by apply/eqP; rewrite eq_le hu hl.
exists c; by split.
Qed.

(** Source for [real_half_null_euclidean_product]: project regression
    for the null-factor clause of Federer 2.10.45, pp. 202-203. Take
    the actual squared Euclidean product R times R, real section degree
    one-half, the whole first factor, and the empty second factor.
    The original coefficient interval is still attained and the product
    mass is zero. No positive-mass premise on V is added. *)
Theorem real_half_null_euclidean_product (R : realType)
    (hk : (0 <= (1/2 : R))%R) :
  let E n := inner_metric_space (@euclidean_inner_productP R n) in
  exists c : R,
    (euclidean_unit_ball_volume R 1)^-1 <=
      c*real_hausdorff_ball_coefficient hk/
        real_hausdorff_ball_coefficient (addr_ge0 hk (ler0n R 1)) /\
    c*real_hausdorff_ball_coefficient hk/
        real_hausdorff_ball_coefficient (addr_ge0 hk (ler0n R 1)) <=
      real_power (Num.sqrt (2:R)) ((1/2 : R)+1%:R)/(2:R) /\
    @real_hausdorff_measure R (E 2%N) ((1/2 : R)+1%:R)%R
      (addr_ge0 hk (ler0n R 1))
      (metric_product_rectangle
        (fun p : E 2 => (@euclidean_block_split R 1 1 p).1)
        (fun p : E 2 => (@euclidean_block_split R 1 1 p).2)
        setT set0) = 0%E.
Proof.
move=> E.
have hV : (@real_hausdorff_measure R (E 1%N) (1/2 : R)%R hk set0 < +oo)%E.
  rewrite (measure_empty (@real_hausdorff_measure_is_measure R (E 1%N) _ hk)); exact: ltry.
have [c [hl [hu he]]] := @federer_2_10_45_real R 1%N (1/2 : R) hk
  (E 2%N) (E 1%N) (fun x y => @euclidean_block_join R 1 1 (x,y))
  (fun p => (@euclidean_block_split R 1 1 p).1)
  (fun p => (@euclidean_block_split R 1 1 p).2)
  (@euclidean_blocks_are_squared_metric_product R 1 1) set0 hV.
exists c; split=> //; split; first by rewrite expr1 in hu.
have h := he setT (measure_measurable_whole (euclidean_lebesgue_is_measure R 1)).
by rewrite (measure_empty (@real_hausdorff_measure_is_measure R (E 1%N) _ hk)) mule0 in h.
Qed.
