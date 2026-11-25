(** Opaque identification of E*=K(Y)* for Federer (1969), 2.5.20, p. 114.
    Only evaluation, Daniell membership, and weak continuity are exposed.
    Source context: CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals topology.
From Federer Require Import CompactFunctionSpaceUP CompactFunctionSpaceLaws
  CompactFunctionDualUP CompactFunctionDualConstruction CompactSupportFunctionUP
  VectorDaniellHypotheses DaniellSpaceWeakTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module Type CompactFunctionDualSignature.
(** Source for [value]: the identification with Daniell
    integrals in Federer 2.5.20, p. 114. *)
Parameter value : forall (R : realType) (Y : topologicalType)
  (E : lmodType R) (ev : E -> Y -> R) (hv : is_compact_function_space ev),
  hausdorff_space Y -> compact (@setT Y) ->
  weak_dual_space (compact_function_norm_laws hv) ->
  daniell_weak_space (@compactly_supported_continuous_functions R Y).
(** Source for [laws]: pairing and topology properties of the
    identification used in Federer 2.5.20, p. 114. *)
Parameter laws : forall (R : realType) (Y : topologicalType)
  (E : lmodType R) (ev : E -> Y -> R) (hv : is_compact_function_space ev)
  (hh : hausdorff_space Y) (hc : compact (@setT Y)),
  is_compact_function_dual_identification ev (@value R Y E ev hv hh hc).
End CompactFunctionDualSignature.

Module CompactFunctionDual : CompactFunctionDualSignature.
(** Source for [value]: selection of the proved witness for
    the identification in Federer 2.5.20, p. 114. *)
Definition value (R : realType) (Y : topologicalType)
  (E : lmodType R) (ev : E -> Y -> R) (hv : is_compact_function_space ev)
  (hh : hausdorff_space Y) (hc : compact (@setT Y)) :=
  sval (cid (@compact_function_dual_identification_exists R Y E ev hv hh hc)).
(** Source for [laws]: the chosen identification satisfies
    its abstract laws, Federer 2.5.20, p. 114. *)
Lemma laws (R : realType) (Y : topologicalType)
  (E : lmodType R) (ev : E -> Y -> R) (hv : is_compact_function_space ev)
  (hh : hausdorff_space Y) (hc : compact (@setT Y)) :
  is_compact_function_dual_identification ev (@value R Y E ev hv hh hc).
Proof. exact: svalP (cid (@compact_function_dual_identification_exists R Y E ev hv hh hc)). Qed.
End CompactFunctionDual.
