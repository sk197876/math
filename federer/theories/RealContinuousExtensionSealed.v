(** Sealed Tietze extensions for Federer (1969), 2.3.6, p. 77. Source
    context and the general-topology dependency:
    RealContinuousExtensionConstruction.v. Downstream arguments use only
    continuous extension and agreement with the given data. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals topology.
From Federer Require Import RealContinuousExtensionUP RealContinuousExtensionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Module Type RealContinuousExtensionSignature.
(** Source for [value]: abstract extension h in the second
    corollary of Federer 2.3.6, p. 77. *)
Parameter value : forall (R : realType) (X : topologicalType), normal_space X ->
  forall C : set X, closed C -> forall f : X -> R^o,
  {within C, continuous f} -> X -> R^o.
(** Source for [laws]: continuity and agreement on C in
    Federer 2.3.6, p. 77. *)
Parameter laws : forall (R : realType) (X : topologicalType) (hn : normal_space X)
  (C : set X) (hC : closed C) (f : X -> R^o) (hf : {within C, continuous f}),
  is_real_continuous_extension C f (@value R X hn C hC f hf).
End RealContinuousExtensionSignature.
Module RealContinuousExtension : RealContinuousExtensionSignature.
(** Source for [value]: private witness selection for the
    Tietze extension cited in Federer 2.3.6, p. 77. *)
Definition value (R : realType) (X : topologicalType) (hn : normal_space X)
    (C : set X) (hC : closed C) (f : X -> R^o) (hf : {within C, continuous f}) :=
  projT1 (cid (@normal_real_continuous_extension_exists R X hn C hC f hf)).
(** Source for [laws]: the selected witness satisfies the
    extension specification for Federer 2.3.6, p. 77. *)
Lemma laws (R : realType) (X : topologicalType) (hn : normal_space X)
    (C : set X) (hC : closed C) (f : X -> R^o) (hf : {within C, continuous f}) :
  is_real_continuous_extension C f (@value R X hn C hC f hf).
Proof. exact: projT2 (cid (@normal_real_continuous_extension_exists R X hn C hC f hf)). Qed.
End RealContinuousExtension.
