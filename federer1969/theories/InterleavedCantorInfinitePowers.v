(** Federer (1969), 2.10.29, p. 195: every positive integer power of the
    interleaved mixed product has infinite degree-k measure for
    0<=k<q*(m+1). Iterate the proved local density product law on the actual
    Euclidean measure powers and use their positive mass on the
    corresponding set powers. The normaliser b>0 remains arbitrary. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  RealMetricBackground RealPower EuclideanRealPlane EuclideanCantorProduct EuclideanCantorProductRegular
  MetricCartesianProductUP MetricRealPowerMeasure MeasureUP BorelRegularMeasureUP
  PowerCantorPairUP PowerCantorPair PowerCantorProductMeasure InterleavedCantorScalesUP InterleavedCantorProductDensity
  PowerCoverDensityUP PowerCoverDensityLaws EuclideanMeasurePowerUP EuclideanMeasurePower
  EuclideanMeasurePowerRegular EuclideanBlockSetPower EuclideanMeasurePowerMass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [interleaved_cantor_positive_power_infinite]: direct
    infinite-measure conclusion for [A(m,n)*A(m,nu)]^q
    in 2.10.29, p. 195. Stage q0 means
    q=q0+1 and has actual Euclidean dimension
    2*q by euclidean_power_dimensionE. The
    orthogonal rearrangement to A(m,n)^q*A(m,nu)^q
    is a separate coordinate identity. *)
Theorem interleaved_cantor_positive_power_infinite (R : realType) (c m : R) D A B f g :
  (0<c)%R -> (0<m)%R -> (m<1)%R ->
  is_interleaved_cantor_scales (fun t=>(c*real_power t m)%R) D ->
  is_power_cantor_pair c m (cantor_left_subdivision D) A f ->
  is_power_cantor_pair c m (cantor_right_subdivision D) B g ->
  forall q0 (b k : R), (0<b)%R -> (0<=k)%R -> (k<q0.+1%:R*(m+1))%R ->
    @metric_real_power_measure R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R (euclidean_power_dimension 2 q0))]
      b k (@euclidean_block_set_power R 2 (euclidean_cantor_product A B) q0)=+oo.
Proof.
move=> hc hm hm1 hD hA hB q0 b k hb hk hgap.
pose E := [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)].
pose nu := @power_cantor_product_measure R E (@euclidean_real_plane_pair R) c m (ltW hc) A B.
pose hn := @power_cantor_product_is_measure R E (@euclidean_real_plane_pair R) c m (ltW hc) A B.
pose C := euclidean_cantor_product A B.
have hcompactA := (power_cantor_pair_properties hc hm hm1 hA).1.
have hcompactB := (power_cantor_pair_properties hc hm hm1 hB).1.
have hr : is_borel_regular_measure nu := @euclidean_cantor_competing_product_borel_regular R c m (ltW hc) A B hcompactA hcompactB.
have hC : measure_measurable nu C.
  apply: (borel_regular_borel_measurable hn hr); exact: euclidean_cantor_product_borel hcompactA hcompactB.
have hpos : 0<nu C.
  rewrite /nu /C /euclidean_cantor_product
    (@power_cantor_product_cantor_mass R E (@euclidean_real_plane_pair R)
      (@euclidean_real_plane_first R) (@euclidean_real_plane_second R) (@euclidean_real_plane_is_metric_product R)
      c m (ltW hc) _ _ A B f g hc hm hm1 hA hB) lte_fin.
  exact (mulr_gt0 hc hc).
have hq : (0<q0.+1%:R :> R)%R by rewrite ltr0n.
pose p := (k/q0.+1%:R)%R.
have hp : (0<=p)%R := divr_ge0 hk (ltW hq).
have hpm : (p<m+1)%R.
  rewrite /p ltr_pdivrMr // mulrC; exact hgap.
have heq : (q0.+1%:R * p=k)%R by rewrite /p mulrC divfK ?gt_eqF.
have hbase : is_vanishing_power_cover_density p nu.
  apply: (@gauge_bounds_give_vanishing_power_density R E p nu hp).
  exact (@interleaved_power_cantor_product_small_density R E (@euclidean_real_plane_pair R)
    (@euclidean_real_plane_first R) (@euclidean_real_plane_second R) (@euclidean_real_plane_is_metric_product R)
    c m p 1%R (ltW hc) D A B f g hc hm hm1 hp hpm ltr01 hD hA hB).
have hdensity := @euclidean_measure_power_vanishing_density R 2 nu hn p hp hr hbase q0.
rewrite heq in hdensity.
have hmass := @euclidean_measure_power_positive_set_power R 2 nu hn C hC hpos q0.
exact (@vanishing_power_density_infinite_measure R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R (euclidean_power_dimension 2 q0))]
  k b (@euclidean_measure_power R 2 nu hn q0) (@euclidean_block_set_power R 2 C q0) hb
  (@euclidean_measure_power_is_measure R 2 nu hn q0) hmass.2 hdensity).
Qed.
