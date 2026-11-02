(** Federer (1969), 2.3.6, p. 77, first corollary: countably many closed
    continuity pieces give Borel inverse images. *)
From mathcomp Require Import all_boot classical_sets topology.
From Federer Require Import PartialFunctionUP PartialContinuityUP
  TopologicalBorel BorelFamilyBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [continuous_closed_piece_borel_preimage]: supporting
    Borel-pasting step for Federer 2.3.6, p. 77. Relative
    continuity on a closed piece gives an ambient Borel inverse image. *)
Lemma continuous_closed_piece_borel_preimage (X Y : topologicalType)
    (C : set X) (f : partial_function X Y) : closed C ->
  partial_function_continuous_on C f -> forall U, open U ->
  borel_set (C `&` partial_function_preimage f U).
Proof.
move=> hC hf U hU; have [V [hV he]] := partial_continuity_open hf hU.
rewrite he; exact: (borel_family_binary_intersection (borel_sets_family X)
  (closed_borel_set hC) (open_borel_set hV)).
Qed.
