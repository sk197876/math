(** Federer 2.10.29, pp. 193-195. Instantiate the existing original
    Cantor-product theorems at the actual Gamma normalizer in every
    real degree. The positive finite powers retain the original Euclidean
    coordinate grouping and every degree 0<=k<q*(m+1). *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerMetric RealMetricBackground RealPower
  RealHausdorffNormalisation RealHausdorffMeasure RealHausdorffCantorPair
  PowerCantorPairUP InterleavedCantorScalesUP InterleavedPowerCantorPairs
  EuclideanCantorProduct PowerCantorSelfProduct EuclideanMeasurePowerUP
  EuclideanSetPowers EuclideanBlockSetPower EuclideanPairPowerShuffle
  CantorPowerProductTheorem.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [power_cantor_self_product_hausdorff_bound]: direct
    Gamma-normalized self-product bound of Federer 2.10.29, p. 193.
    The right side is alpha(2m)*2^(-m), written as the degree-2m
    diameter-cost normalizer times 2^m. The original Cantor pair is
    characterized by its recurrence; no new set is constructed. *)
Theorem power_cantor_self_product_hausdorff_bound (R : realType)
    (m : R) (hm : (0<m)%R) (hm1 : (m<1)%R) n A f :
    is_power_cantor_pair (real_hausdorff_normalisation (ltW hm)) m n A f ->
    let hp := mulr_ge0 (ler0n R 2) (ltW hm) in
    @real_hausdorff_measure R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)]
      (2* m)%R hp (euclidean_cantor_product A A)<=
      (real_hausdorff_normalisation hp * real_power 2 m)%R%:E.
Proof.
move=> hpair.
pose hp := mulr_ge0 (ler0n R 2) (ltW hm).
exact: (@power_cantor_self_product_bound R
  (real_hausdorff_normalisation (ltW hm)) m (real_hausdorff_normalisation hp)
  n A f (real_hausdorff_normalisation_positive (ltW hm)) hm hm1
  (ltW (real_hausdorff_normalisation_positive hp)) hpair).
Qed.

(** Source for [federer_2_10_29_real_degree]: direct complete
    Gamma-normalized product conclusions of Federer 2.10.29,
    pp. 193-195. Choose the original interleaved Cantor pairs at
    alpha(m)*2^(-m). Both have exactly that positive degree-m mass;
    both self-products satisfy the printed finite bound. Every positive
    finite power has finite degree-qm Hausdorff mass, while its product
    with the other power has infinite degree-k mass for every original
    0<=k<q*(m+1). The witnesses are fixed before q and k are chosen. *)
Theorem federer_2_10_29_real_degree (R : realType) (m : R)
    (hm : (0<m)%R) (hm1 : (m<1)%R) :
    let c := real_hausdorff_normalisation (ltW hm) in
    let hp2 := mulr_ge0 (ler0n R 2) (ltW hm) in
    exists (D : interleaved_cantor_scale_data R)
      (A B : set (real_line_metric R)) (f g : R -> R),
      is_interleaved_cantor_scales (fun t => (c*real_power t m)%R) D /\
      is_power_cantor_pair c m (cantor_left_subdivision D) A f /\
      is_power_cantor_pair c m (cantor_right_subdivision D) B g /\
      @real_hausdorff_measure R [the metricType R of real_line_metric R]
        m (ltW hm) A=c%:E /\
      @real_hausdorff_measure R [the metricType R of real_line_metric R]
        m (ltW hm) B=c%:E /\
      @real_hausdorff_measure R
        [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)]
        (2* m)%R hp2 (euclidean_cantor_product A A)<=
        (real_hausdorff_normalisation hp2*real_power 2 m)%R%:E /\
      @real_hausdorff_measure R
        [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)]
        (2* m)%R hp2 (euclidean_cantor_product B B)<=
        (real_hausdorff_normalisation hp2*real_power 2 m)%R%:E /\
      forall q,
        let hq := mulr_ge0 (ler0n R q.+1) (ltW hm) in
        @real_hausdorff_measure R
          [the metricType R of inner_metric_space (@euclidean_inner_productP R q.+1)]
          (q.+1%:R* m)%R hq (euclidean_set_power q.+1 A)<=
          (real_hausdorff_normalisation hq*
            real_power q.+1%:R (q.+1%:R* m))%R%:E /\
        @real_hausdorff_measure R
          [the metricType R of inner_metric_space (@euclidean_inner_productP R q.+1)]
          (q.+1%:R* m)%R hq (euclidean_set_power q.+1 B)<=
          (real_hausdorff_normalisation hq*
            real_power q.+1%:R (q.+1%:R* m))%R%:E /\
        forall (k : R) (hk : (0<=k)%R), (k<q.+1%:R*(m+1))%R ->
          @real_hausdorff_measure R
            [the metricType R of inner_metric_space
              (@euclidean_inner_productP R (q.+1+q.+1))]
            k hk (@euclidean_power_product R q.+1 A B)=+oo.
Proof.
move=> c hp2.
have hc : (0<c)%R := real_hausdorff_normalisation_positive (ltW hm).
have [D [A [B [f [g [hD [hA [hB hpowers]]]]]]]] :=
  @federer_2_10_29_positive_powers R c m hc hm hm1.
exists D,A,B,f,g; split=> //; split=> //; split=> //.
split; first exact: (@power_cantor_pair_hausdorff_mass R m (ltW hm)
  (cantor_left_subdivision D) A f hm hm1 hA).1.
split; first exact: (@power_cantor_pair_hausdorff_mass R m (ltW hm)
  (cantor_right_subdivision D) B g hm hm1 hB).1.
split; first exact: (@power_cantor_self_product_hausdorff_bound R m hm hm1
  (cantor_left_subdivision D) A f hA).
split; first exact: (@power_cantor_self_product_hausdorff_bound R m hm hm1
  (cantor_right_subdivision D) B g hB).
move=> q hq.
have [hleft [hright _]] := hpowers q (real_hausdorff_normalisation hq)
  (real_hausdorff_normalisation_positive hq).
split=> //; split=> // k hk hgap.
have [_ [_ hprod]] := hpowers q (real_hausdorff_normalisation hk)
  (real_hausdorff_normalisation_positive hk).
exact: hprod k hk hgap.
Qed.
