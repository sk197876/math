(** Federer (1969), 3.2.40, p. 276: the actual
    subcritical same-factor Cantor square has zero Hausdorff
    length. This uses the already proved finite square-cover
    power cost of 2.10.29, p. 193. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground EuclideanInnerProduct InnerMetric
  EuclideanCantorProduct PowerCantorPairUP PowerCantorSelfProduct
  MetricRealPowerMeasure RealPower FiniteSubunitPowerLengthNull
  HausdorffMeasure HausdorffLengthCompatibility.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [subcritical_cantor_square_Hausdorff_null]: the
    Hausdorff-null statement for 0<m<1/2 in Federer
    3.2.40, p. 276. The true finite unit-coefficient
    2m-power square-cover mass implies zero actual Hausdorff
    length by the proved cost comparison. The degree-one
    normalization is already identified; no fractional
    Gamma normalization or rectifiability is assumed. *)
Theorem subcritical_cantor_square_Hausdorff_null (R:realType) (c m:R)
    (n:nat->nat) (A:set (real_line_metric R)) (f:R->R):
  (0<c)%R ->(0<m)%R ->(m<1/2)%R ->is_power_cantor_pair c m n A f ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2)) 1
    (euclidean_cantor_product A A)=0.
Proof.
move=>hc hm hmHalf hPair.
have hm1:(m<1)%R by lra.
have hTwo:(0<(2:R))%R by rewrite ltr0n.
have hDegree:(0<2 * m)%R:=mulr_gt0 hTwo hm.
have hDegree1:(2 * m<1)%R by lra.
have hBound:=@power_cantor_self_product_bound R c m 1 n A f hc hm hm1 ler01 hPair.
rewrite mul1r in hBound.
have hFinite:@metric_real_power_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)]
    1 (2 * m)%R (euclidean_cantor_product A A) < +oo.
  exact:le_lt_trans hBound (ltry _).
rewrite hausdorff_measure_one_length.
exact:(@finite_subunit_power_mass_zero_length R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)]
  (2 * m)%R (euclidean_cantor_product A A) hDegree hDegree1 hFinite).
Qed.
