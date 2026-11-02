(** Public identification of E* with Daniell integrals for Federer (1969),
    2.5.20, p. 114. This module uses only the sealed specification. Source
    context: CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals topology.
From Federer Require Import CompactFunctionSpaceUP CompactFunctionSpaceLaws
  CompactFunctionDualUP CompactFunctionDualSealed CompactSupportFunctionUP
  VectorDaniellHypotheses DaniellSpaceWeakTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_function_dual_map]: the identification
    with Daniell integrals used in Federer 2.5.20, p. 114. *)
Definition compact_function_dual_map (R : realType) (Y : topologicalType)
  (E : lmodType R) (ev : E -> Y -> R) (hv : is_compact_function_space ev)
  (hh : hausdorff_space Y) (hc : compact (@setT Y)) :=
  @CompactFunctionDual.value R Y E ev hv hh hc.

(** Source for [compact_function_dual_map_specification]:
    pairing, Daniell membership, and weak continuity of the
    identification in Federer 2.5.20, p. 114. *)
Theorem compact_function_dual_map_specification (R : realType) (Y : topologicalType)
  (E : lmodType R) (ev : E -> Y -> R) (hv : is_compact_function_space ev)
  (hh : hausdorff_space Y) (hc : compact (@setT Y)) :
  is_compact_function_dual_identification ev (@compact_function_dual_map R Y E ev hv hh hc).
Proof. exact (@CompactFunctionDual.laws R Y E ev hv hh hc). Qed.
