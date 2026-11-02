(** Federer (1969), 2.10.29, p. 195: the product A(m,n)^q*A(m,nu)^q has
    infinite degree-k measure for 0<=k<q*(m+1), although each scalar power
    has finite degree-qm measure. Transfer the already proved infinity of
    the power of pairs through the sealed orthogonal coordinate
    identification. Positive normalising coefficients remain explicit,
    independently of the pending analytic Gamma definition. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  RealMetricBackground RealPower MetricRealPowerMeasure MetricRealPowerMaps
  EuclideanMeasurePowerUP EuclideanBlockSetPower EuclideanSetPowers EuclideanCantorProduct EuclideanPairPowerShuffle
  PowerCantorPairUP InterleavedCantorScalesUP InterleavedPowerCantorPairs PowerCantorFinitePowers InterleavedCantorInfinitePowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_power_product_measure]: direct
    equality of the two identified product
    measures in 2.10.29, p. 195, for
    any nonnegative real degree and coefficient.
    It uses the proved metric isometry, with
    no construction of a new metric. *)
Theorem euclidean_power_product_measure (R : realType) q (b k : R) (A B : set (real_line_metric R)) :
  (0<=b)%R -> (0<=k)%R ->
  @metric_real_power_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R (q.+1+q.+1))]
    b k (@euclidean_power_product R q.+1 A B)=
  @metric_real_power_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R (euclidean_power_dimension 2 q))]
    b k (@euclidean_block_set_power R 2 (euclidean_cantor_product A B) q).
Proof.
move=> hb hk.
have hf x y : (mdist (@euclidean_power_regroup R q x) (@euclidean_power_regroup R q y)<=mdist x y)%R.
  by rewrite euclidean_power_regroup_distance.
have hg x y : (mdist (@euclidean_power_ungroup R q x) (@euclidean_power_ungroup R q y)<=mdist x y)%R.
  by rewrite euclidean_power_ungroup_distance.
have hh := @metric_real_power_isometric_image R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R (q.+1+q.+1))]
  [the metricType R of inner_metric_space (@euclidean_inner_productP R (euclidean_power_dimension 2 q))]
  b k (@euclidean_power_regroup R q) (@euclidean_power_ungroup R q) hb hk
  (@euclidean_power_regroupK R q) hf hg (@euclidean_power_product R q.+1 A B).
by rewrite euclidean_power_regroup_image in hh; exact: esym hh.
Qed.

(** Source for [interleaved_cantor_power_product_infinite]: direct
    final infinite-measure assertion for A^q*B^q
    in 2.10.29, p. 195. Both factors
    and the ambient metric are the actual
    Euclidean ones. The integer q is positive. *)
Theorem interleaved_cantor_power_product_infinite (R : realType) (c m : R) D A B f g :
  (0<c)%R -> (0<m)%R -> (m<1)%R ->
  is_interleaved_cantor_scales (fun t=>(c*real_power t m)%R) D ->
  is_power_cantor_pair c m (cantor_left_subdivision D) A f ->
  is_power_cantor_pair c m (cantor_right_subdivision D) B g ->
  forall q (b k : R), (0<b)%R -> (0<=k)%R -> (k<q.+1%:R*(m+1))%R ->
    @metric_real_power_measure R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R (q.+1+q.+1))]
      b k (@euclidean_power_product R q.+1 A B)=+oo.
Proof.
move=> hc hm hm1 hD hA hB q b k hb hk hgap.
rewrite (@euclidean_power_product_measure R q b k A B (ltW hb) hk).
exact (@interleaved_cantor_positive_power_infinite R c m D A B f g hc hm hm1 hD hA hB q b k hb hk hgap).
Qed.

(** Source for [federer_2_10_29_positive_powers]: direct
    simultaneous finite-factor and infinite-product
    conclusions for every positive integer q
    in 2.10.29, p. 195. The actual
    Cantor pairs and scales are chosen before
    any degree or normaliser of the conclusion. *)
Theorem federer_2_10_29_positive_powers (R : realType) (c m : R) :
  (0<c)%R -> (0<m)%R -> (m<1)%R ->
  exists (D : interleaved_cantor_scale_data R) (A B : set (real_line_metric R)) (f g : R -> R),
    is_interleaved_cantor_scales (fun t=>(c*real_power t m)%R) D /\
    is_power_cantor_pair c m (cantor_left_subdivision D) A f /\
    is_power_cantor_pair c m (cantor_right_subdivision D) B g /\
    forall q (b : R), (0<b)%R ->
      (@metric_real_power_measure R
        [the metricType R of inner_metric_space (@euclidean_inner_productP R q.+1)]
        b (q.+1%:R * m)%R (euclidean_set_power q.+1 A)<=
          (b*real_power q.+1%:R (q.+1%:R * m))%R%:E) /\
      (@metric_real_power_measure R
        [the metricType R of inner_metric_space (@euclidean_inner_productP R q.+1)]
        b (q.+1%:R * m)%R (euclidean_set_power q.+1 B)<=
          (b*real_power q.+1%:R (q.+1%:R * m))%R%:E) /\
      forall k : R, (0<=k)%R -> (k<q.+1%:R*(m+1))%R ->
        @metric_real_power_measure R
          [the metricType R of inner_metric_space (@euclidean_inner_productP R (q.+1+q.+1))]
          b k (@euclidean_power_product R q.+1 A B)=+oo.
Proof.
move=> hc hm hm1.
have [D [A [B [f [g [hD [hA hB]]]]]]] := interleaved_power_cantor_pairs_exist hc hm hm1.
exists D,A,B,f,g; split=> //; split=> //; split=> //; move=> q b hb.
split; first exact (@power_cantor_positive_cartesian_power_bound R c m b _ A f q hc hm hm1 (ltW hb) hA).
split; first exact (@power_cantor_positive_cartesian_power_bound R c m b _ B g q hc hm hm1 (ltW hb) hB).
move=> k hk hgap.
exact (@interleaved_cantor_power_product_infinite R c m D A B f g hc hm hm1 hD hA hB q b k hb hk hgap).
Qed.
