(** Federer (1969), 2.10.29, pp. 194–195: the interleaved Cantor product has
    infinite k-dimensional covering measure for 0<=k<m+1. The proof uses its
    actual positive product mass, the proved vanishing local density, and
    the abstract covering infimum. It holds for every positive real
    power-gauge coefficient, before Euler-Gamma normalisation is selected. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground RealPower MetricCartesianProductUP
  MetricRealPowerMeasure PowerCantorPairUP PowerCantorProductMeasure
  InterleavedCantorScalesUP InterleavedPowerCantorPairs InterleavedCantorProductDensity
  CaratheodoryVanishingDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [interleaved_power_cantor_product_infinite]: direct
    mixed-product infinity assertion of 2.10.29,
    p. 194, including k=0 as in the final
    statement on p. 195. The target normaliser
    b>0 remains explicit and independent of c. *)
Theorem interleaved_power_cantor_product_infinite (R : realType) (P : metricType R)
    (pair : real_line_metric R -> real_line_metric R -> P)
    (first second : P -> real_line_metric R)
    (hp : is_metric_cartesian_product pair first second)
    (c m : R) D A B f g :
  (0<c)%R -> (0<m)%R -> (m<1)%R ->
  is_interleaved_cantor_scales (fun t=>(c*real_power t m)%R) D ->
  is_power_cantor_pair c m (cantor_left_subdivision D) A f ->
  is_power_cantor_pair c m (cantor_right_subdivision D) B g ->
  forall (b k : R), (0<b)%R -> (0<=k)%R -> (k<m+1)%R ->
    @metric_real_power_measure R P b k [set p | A (first p) /\ B (second p)]=+oo.
Proof.
move=> hc hm hm1 hD hA hB b k hb hk hgap.
pose nu := @power_cantor_product_measure R P pair c m (ltW hc) A B.
have hnu := @power_cantor_product_is_measure R P pair c m (ltW hc) A B.
have hpos : 0<nu [set p | A (first p) /\ B (second p)].
  rewrite /nu (@power_cantor_product_cantor_mass R P pair first second hp c m (ltW hc)
    _ _ A B f g hc hm hm1 hA hB) lte_fin; exact (mulr_gt0 hc hc).
apply: (@caratheodory_vanishing_generator_density R P _ _ _ _ nu _
  (@metric_real_power_measure_specification R P b k) hnu hpos)=> e he.
have [d [hd hbound]] := @interleaved_power_cantor_product_small_density R P pair first second hp
  c m k b (ltW hc) D A B f g hc hm hm1 hk hgap hb hD hA hB e he.
exists d; split=> // S hdiam; exact (hbound (val S) hdiam).
Qed.

(** Source for [interleaved_infinite_power_cantor_product_exists]: direct
    existence of the mixed product in 2.10.29,
    p. 194, with both actual Cantor pairs.
    The finite self-product and higher Cartesian
    power conclusions are separate statements. *)
Theorem interleaved_infinite_power_cantor_product_exists (R : realType) (P : metricType R)
    (pair : real_line_metric R -> real_line_metric R -> P)
    (first second : P -> real_line_metric R)
    (hp : is_metric_cartesian_product pair first second) (c m : R) :
  (0<c)%R -> (0<m)%R -> (m<1)%R ->
  exists (D : interleaved_cantor_scale_data R) (A B : set (real_line_metric R)) (f g : R -> R),
    is_interleaved_cantor_scales (fun t=>(c*real_power t m)%R) D /\
    is_power_cantor_pair c m (cantor_left_subdivision D) A f /\
    is_power_cantor_pair c m (cantor_right_subdivision D) B g /\
    forall (b k : R), (0<b)%R -> (0<=k)%R -> (k<m+1)%R ->
      @metric_real_power_measure R P b k [set p | A (first p) /\ B (second p)]=+oo.
Proof.
move=> hc hm hm1.
have [D [A [B [f [g [hD [hA hB]]]]]]] := interleaved_power_cantor_pairs_exist hc hm hm1.
exists D,A,B,f,g; split=> //; split=> //; split=> //.
exact (@interleaved_power_cantor_product_infinite R P pair first second hp c m D A B f g hc hm hm1 hD hA hB).
Qed.
