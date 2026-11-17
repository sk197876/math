(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 320: opaque
    var(I), specified by every original finite generator system. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import HolomorphicUP ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP NormMetric HolomorphicGermUP HolomorphicGermRing SetGermUP
  CommutativeIdealUP HolomorphicIdealVarietyGermUP HolomorphicIdealVarietyGermExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type IdealVarietyGermSignature.
(** Source for [value]: var(I) for an actually finitely
    generated ideal, 3.4.5, p. 320. *)
Parameter value:forall (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R)
  (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X)
  (I:set [the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)]),
  is_finitely_generated_commutative_ideal I ->
    @set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a.
(** Source for [laws]: the original all-generator
    characterization of var(I), 3.4.5, p. 320. *)
Parameter laws:forall (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R)
  (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X)
  (I:set [the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)])
  (hI:is_finitely_generated_commutative_ideal I),
  @is_holomorphic_ideal_variety_germ R X NX hNX a I (@value R X NX hNX a I hI).
End IdealVarietyGermSignature.
Module HolomorphicIdealVarietyGerm:IdealVarietyGermSignature.
(** Source for [value]: private witness of the proved
    unique existence theorem, 3.4.5, p. 320. *)
Definition value (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R)
    (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X)
    (I:set [the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)])
    (hI:is_finitely_generated_commutative_ideal I):=
  projT1 (cid (@holomorphic_ideal_variety_germ_exists R X NX hNX a I hI)).
(** Source for [laws]: the selected witness satisfies
    every original generator equation, 3.4.5, p. 320. *)
Lemma laws (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R)
    (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X)
    (I:set [the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)])
    (hI:is_finitely_generated_commutative_ideal I):
  @is_holomorphic_ideal_variety_germ R X NX hNX a I (@value R X NX hNX a I hI).
Proof. exact:(projT2 (cid (@holomorphic_ideal_variety_germ_exists R X NX hNX a I hI))). Qed.
End HolomorphicIdealVarietyGerm.
