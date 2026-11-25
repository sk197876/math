(** Federer (1969), 2.10.29, p. 194: the interleaved product as an actual
    subset of R^2. Apply the abstract product proof to the existing
    Euclidean coordinate maps. Every positive real power-gauge coefficient
    is allowed. At degree one, the independently proved unit normalisation
    identifies the measure with Hausdorff length. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  RealMetricBackground RealPower EuclideanRealPlane MetricRealPowerMeasure MetricRealPowerLength HausdorffLength
  PowerCantorPairUP InterleavedCantorScalesUP InterleavedCantorProductInfinite.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section PlaneProduct.
Variable R : realType.
Local Notation E := (inner_metric_space (@euclidean_inner_productP R 2)).

(** Source for [euclidean_cantor_product]: direct
    set A(m,n) times A(m,nu) in 2.10.29,
    p. 194, using the actual two Euclidean
    coordinates rather than a replacement metric. *)
Definition euclidean_cantor_product (A B : set (real_line_metric R)) : set E :=
  [set p | A (euclidean_real_plane_first p) /\ B (euclidean_real_plane_second p)].

(** Source for [euclidean_interleaved_cantor_product_infinite]: direct
    infinite k-dimensional power-gauge measure for
    the interleaved Euclidean product in 2.10.29,
    p. 194, including k=0 as on p. 195.
    The coefficient b is arbitrary and positive. *)
Theorem euclidean_interleaved_cantor_product_infinite (c m : R) D A B f g :
  (0<c)%R -> (0<m)%R -> (m<1)%R ->
  is_interleaved_cantor_scales (fun t=>(c*real_power t m)%R) D ->
  is_power_cantor_pair c m (cantor_left_subdivision D) A f ->
  is_power_cantor_pair c m (cantor_right_subdivision D) B g ->
  forall (b k : R), (0<b)%R -> (0<=k)%R -> (k<m+1)%R ->
    @metric_real_power_measure R [the metricType R of E] b k (euclidean_cantor_product A B)=+oo.
Proof.
exact (@interleaved_power_cantor_product_infinite R [the metricType R of E]
  (@euclidean_real_plane_pair R) (@euclidean_real_plane_first R) (@euclidean_real_plane_second R)
  (@euclidean_real_plane_is_metric_product R) c m D A B f g).
Qed.

(** Source for [euclidean_interleaved_cantor_product_infinite_length]: direct
    k=1 consequence of 2.10.29, p. 194,
    for every 0<m<1. The measure is the
    existing Hausdorff length with its proved
    unit coefficient, so this corollary needs
    no real-degree Gamma identification. *)
Theorem euclidean_interleaved_cantor_product_infinite_length (c m : R) D A B f g :
  (0<c)%R -> (0<m)%R -> (m<1)%R ->
  is_interleaved_cantor_scales (fun t=>(c*real_power t m)%R) D ->
  is_power_cantor_pair c m (cantor_left_subdivision D) A f ->
  is_power_cantor_pair c m (cantor_right_subdivision D) B g ->
  @hausdorff_length R [the metricType R of E] (euclidean_cantor_product A B)=+oo.
Proof.
move=> hc hm hm1 hD hA hB.
have hgap : (1<m+1)%R by rewrite ltrDr.
have hh := @euclidean_interleaved_cantor_product_infinite c m D A B f g hc hm hm1 hD hA hB
  1%R 1%R ltr01 ler01 hgap.
by rewrite metric_real_power_measure_length_agreement in hh.
Qed.

(** Source for [euclidean_infinite_power_cantor_product_exists]: direct
    existence of the interleaved product of
    2.10.29, p. 194, in the actual
    Euclidean plane, with both Cantor pairs
    specified independently of the infinity conclusion. *)
Theorem euclidean_infinite_power_cantor_product_exists (c m : R) :
  (0<c)%R -> (0<m)%R -> (m<1)%R ->
  exists (D : interleaved_cantor_scale_data R) (A B : set (real_line_metric R)) (f g : R -> R),
    is_interleaved_cantor_scales (fun t=>(c*real_power t m)%R) D /\
    is_power_cantor_pair c m (cantor_left_subdivision D) A f /\
    is_power_cantor_pair c m (cantor_right_subdivision D) B g /\
    forall (b k : R), (0<b)%R -> (0<=k)%R -> (k<m+1)%R ->
      @metric_real_power_measure R [the metricType R of E] b k (euclidean_cantor_product A B)=+oo.
Proof.
exact (@interleaved_infinite_power_cantor_product_exists R [the metricType R of E]
  (@euclidean_real_plane_pair R) (@euclidean_real_plane_first R) (@euclidean_real_plane_second R)
  (@euclidean_real_plane_is_metric_product R) c m).
Qed.
End PlaneProduct.
