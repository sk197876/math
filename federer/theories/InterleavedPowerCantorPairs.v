(** Federer (1969), 2.10.29, pp. 193–194: construct the two power Cantor
    sets using the interleaved subdivision schedules. The normalising
    coefficient c remains explicit. Existence uses only the proved opaque
    scale, interval-tree, limit and cumulative interfaces; no
    product-measure conclusion is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground RealPower PowerConcaveIntervalGauge PowerCantorPairUP
  PowerCantorPair InterleavedCantorScalesUP InterleavedCantorScales.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [power_cantor_pairs_for_interleaved_scales]: supporting
    existence of both Cantor sets in 2.10.29,
    p. 194, for any scales satisfying
    the abstract interleaved laws. Their
    cumulative functions retain the value laws
    already proved in 2.10.28, p. 193. *)
Theorem power_cantor_pairs_for_interleaved_scales (R : realType) (c m : R)
    (D : interleaved_cantor_scale_data R) :
  0<c -> 0<m -> m<1 -> is_interleaved_cantor_scales (fun t=>c*real_power t m) D ->
  exists (A B : set (real_line_metric R)) (f g : R -> R),
    is_power_cantor_pair c m (cantor_left_subdivision D) A f /\
    is_power_cantor_pair c m (cantor_right_subdivision D) B g.
Proof.
move=> hc hm hm1 hD.
have [A [f hA]] := @power_cantor_pair_exists R c m (cantor_left_subdivision D) hc hm hm1
  (interleaved_cantor_left_count hD).
have [B [g hB]] := @power_cantor_pair_exists R c m (cantor_right_subdivision D) hc hm hm1
  (interleaved_cantor_right_count hD).
exists A,B,f,g; by split.
Qed.

(** Source for [interleaved_power_cantor_pairs_exist]: direct
    existence of the two interleaved Cantor
    constructions used in 2.10.29, p. 194,
    with their defining scale and limit laws.
    The finite/infinite product estimates are
    separate conclusions still to prove. *)
Theorem interleaved_power_cantor_pairs_exist (R : realType) (c m : R) :
  0<c -> 0<m -> m<1 ->
  exists (D : interleaved_cantor_scale_data R) (A B : set (real_line_metric R)) (f g : R -> R),
    is_interleaved_cantor_scales (fun t=>c*real_power t m) D /\
    is_power_cantor_pair c m (cantor_left_subdivision D) A f /\
    is_power_cantor_pair c m (cantor_right_subdivision D) B g.
Proof.
move=> hc hm hm1.
have hg := @power_concave_interval_gauge R c m hc hm hm1.
pose D := @interleaved_cantor_scales R _ hg.
have hD := @interleaved_cantor_scales_specification R _ hg.
have [A [B [f [g hAB]]]] := @power_cantor_pairs_for_interleaved_scales R c m D hc hm hm1 hD.
exists D,A,B,f,g; by split.
Qed.
