(** Federer (1969), 2.5.14, p. 107: measurable open sets form a base for the
    topology. This conclusion requires no countable ambient base. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionUP CompactSupportLevels CompactSupportOpenBase
  FunctionLatticeLevelMeasurability RealIntegralFunctionalUP MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [compact_support_representing_measure_open_base]: the
    measurable-open-base assertion in Federer 2.5.14, p. 107 In fact any
    measure representing the integral on K(X) has this base; lattice
    regularity is not needed for the local assertion. *)
Theorem compact_support_representing_measure_open_base (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (A : (X -> R) -> R) (hm : is_measure mu)
    (hA : is_real_integral_functional mu (@compactly_supported_continuous_functions R X) A) :
  hausdorff_space X -> locally_compact (@setT X) -> forall V, open V -> forall x, V x ->
  exists U, open U /\ measure_measurable mu U /\ U x /\ U `<=` V.
Proof.
move=> hh hl V hV x hx.
have [U [hU [hUx hUV]]] := @compact_support_strict_levels_refine_open R X hh hl V hV x hx.
exists U; split; first exact: compact_support_strict_level_open hU.
split; first exact: (@represented_lattice_strict_level_measurable R X _ A mu hm hA U hU).
by split.
Qed.
