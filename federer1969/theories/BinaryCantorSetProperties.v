(** Federer (1969), 3.3.20, p. 306:
    original compactness, nullity and coefficient-independent carrier. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground PowerCantorPairUP PowerCantorPair
  PowerCantorCarrierCoefficient BinaryCantorSetUP LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_power_cantor_original_properties]: the
    factor in 3.3.20, p. 306, is compact,
    contained in [0,1] and Lebesgue null. These
    are actual 2.10.28 conclusions, not defining laws. *)
Theorem binary_power_cantor_original_properties (R:realType) (m:R)
    (A:set (real_line_metric R)):
  0<m ->m<1 ->is_binary_power_cantor_set m A ->
  compact A /\A `<=` (`[0,1]:set (real_line_metric R)) /\lebesgue_scalar_measure A=0%E.
Proof.
move=>hm hm1 [f hPair].
have h:=@power_cantor_pair_properties R 1 m (fun _:nat=>2%N) A f ltr01 hm hm1 hPair.
split;first exact:h.1.
split;first exact:h.2.1.
exact:h.2.2.2.2.2.2.2.1.
Qed.

(** Source for [binary_power_cantor_original_coefficient]: the
    actual carrier remains the printed A(m,n) of
    3.3.20, p. 306, for EVERY positive gauge
    coefficient, including alpha(m)2^(-m). The proved
    coefficient invariance preserves original interval levels
    and the limit; only a local cumulative function changes. *)
Theorem binary_power_cantor_original_coefficient (R:realType) (m c:R)
    (A:set (real_line_metric R)):
  0<m ->m<1 ->0<c ->is_binary_power_cantor_set m A ->
  exists f,is_power_cantor_pair c m (fun _:nat=>2%N) A f.
Proof.
move=>hm hm1 hc [f hPair].
exact:(@power_cantor_carrier_coefficient_change R 1 c m (fun _:nat=>2%N) A f
  ltr01 hc hm hm1 hPair).
Qed.
