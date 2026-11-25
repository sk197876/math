(** Concrete noninteger-degree regressions for Federer 2.10.29,
    pp. 193-195. The original half-degree factors have finite canonical
    mass; their actual Euclidean product has both infinite counting mass
    and infinite canonical degree-one mass. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import FiniteCoordinates EuclideanInnerProduct InnerMetric
  RealMetricBackground RealHausdorffNormalisation RealHausdorffMeasure
  RealHausdorffCantorProducts EuclideanSetPowers EuclideanPairPowerShuffle.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [half_degree_interleaved_hausdorff_products]: regression
    for the interleaved example of Federer 2.10.29, pp. 193-195.
    Choose the actual half-degree Cantor factors once. Each has mass
    alpha(1/2)*2^(-1/2), while their Euclidean product has infinite
    degree-zero and degree-one Hausdorff mass. This checks the zero
    target degree as well as a positive target degree. *)
Theorem half_degree_interleaved_hausdorff_products (R : realType)
    (hhalf : (0<1/2 :> R)%R) :
    let hp := ltW hhalf in
    let c := real_hausdorff_normalisation hp in
    exists (A B : set (real_line_metric R)),
      @real_hausdorff_measure R [the metricType R of real_line_metric R]
        (1/2 : R) hp A=c%:E /\
      @real_hausdorff_measure R [the metricType R of real_line_metric R]
        (1/2 : R) hp B=c%:E /\
      @real_hausdorff_measure R
        [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)]
        0%R (lexx (0%R : R)) (@euclidean_power_product R 1 A B)=+oo /\
      @real_hausdorff_measure R
        [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)]
        1%R (ler01 : (0<=1 :> R)%R) (@euclidean_power_product R 1 A B)=+oo.
Proof.
move=> hp c.
have hhalf1 : (1/2<1 :> R)%R by lra.
have hfull := @federer_2_10_29_real_degree R (1/2 : R) hhalf hhalf1.
case: hfull => D [A [B [f [g h]]]].
case: h => hD [hA [hB [hAm [hBm [hAA [hBB hP]]]]]].
exists A,B; split=> //; split=> //.
have [_ [_ hprod]] := hP 0%N.
split.
- apply: hprod; by rewrite mul1r; lra.
- apply: hprod; by rewrite mul1r; lra.
Qed.
