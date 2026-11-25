(** Federer (1969), 2.10.29, pp. 193–194: combine the finite self-product
    covers and the interleaved mixed-product infinity theorem for actual
    Euclidean Cantor sets. Their factor masses are c>0. All positive target
    normalisers are explicit, so the qualitative conclusions are independent
    of the pending Euler-Gamma formula. The final higher Cartesian-power
    paragraph on p. 195 is separate. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  RealMetricBackground RealPower MetricRealPowerMeasure MetricRealPowerIntervalAgreement
  PowerCantorPairUP InterleavedCantorScalesUP InterleavedPowerCantorPairs EuclideanCantorProduct PowerCantorSelfProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_2_10_29_interleaved_products]: direct
    Cantor product conclusions on pp. 193–194
    of 2.10.29: each factor has mass c,
    its Euclidean self-product has finite degree-2m
    mass, and the mixed product has infinite
    degree-k mass for 0<=k<m+1. All conclusions
    are proved from independent Cantor pair laws.
    The later positive-integer q generalisation is
    not part of this theorem. *)
Theorem federer_2_10_29_interleaved_products (R : realType) (c m : R) :
  (0<c)%R -> (0<m)%R -> (m<1)%R ->
  exists (D : interleaved_cantor_scale_data R) (A B : set (real_line_metric R)) (f g : R -> R),
    is_interleaved_cantor_scales (fun t=>(c*real_power t m)%R) D /\
    is_power_cantor_pair c m (cantor_left_subdivision D) A f /\
    is_power_cantor_pair c m (cantor_right_subdivision D) B g /\
    @metric_real_power_measure R [the metricType R of real_line_metric R] c m A=c%:E /\
    @metric_real_power_measure R [the metricType R of real_line_metric R] c m B=c%:E /\
    forall b : R, (0<b)%R ->
      (@metric_real_power_measure R [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)]
        b (2 * m)%R (euclidean_cantor_product A A)<=(b*real_power 2 m)%R%:E) /\
      (@metric_real_power_measure R [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)]
        b (2 * m)%R (euclidean_cantor_product B B)<=(b*real_power 2 m)%R%:E) /\
      forall k : R, (0<=k)%R -> (k<m+1)%R ->
        @metric_real_power_measure R [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)]
          b k (euclidean_cantor_product A B)=+oo.
Proof.
move=> hc hm hm1.
have [D [A [B [f [g [hD [hA hB]]]]]]] := interleaved_power_cantor_pairs_exist hc hm hm1.
exists D,A,B,f,g; split=> //; split=> //; split=> //; split.
- exact: (power_cantor_pair_real_power_mass hc hm hm1 hA).1.
split; first exact: (power_cantor_pair_real_power_mass hc hm hm1 hB).1.
move=> b hb; split.
- exact (@power_cantor_self_product_bound R c m b _ A f hc hm hm1 (ltW hb) hA).
split.
- exact (@power_cantor_self_product_bound R c m b _ B g hc hm hm1 (ltW hb) hB).
move=> k hk hgap.
exact (@euclidean_interleaved_cantor_product_infinite R c m D A B f g hc hm hm1 hD hA hB b k hb hk hgap).
Qed.
