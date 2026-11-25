(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 320: opaque
    one-equation zero germs with independent representative laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP NormMetric HolomorphicGermUP SetGermUP HolomorphicZeroGermUP HolomorphicZeroGermExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type HolomorphicZeroGermSignature.
(** Source for [value]: the original zero variety germ
    of an analytic equation, 3.4.5, p. 320. *)
Parameter value:forall (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R)
  (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X),holomorphic_germ_space hNX a->
    @set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a.
(** Source for [laws]: every original representative has
    the same zero-set germ, 3.4.5, p. 320. *)
Parameter laws:forall (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R)
  (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X) alpha,
  @is_holomorphic_zero_germ R X NX hNX a alpha (@value R X NX hNX a alpha).
End HolomorphicZeroGermSignature.
Module HolomorphicZeroGerm:HolomorphicZeroGermSignature.
(** Source for [value]: private choice after proved
    existence and uniqueness, 3.4.5, p. 320. *)
Definition value (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R)
    (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X) alpha:=
  projT1 (cid (@holomorphic_zero_germ_exists R X NX hNX a alpha)).
(** Source for [laws]: the witness satisfies the
    independent original representative law, 3.4.5, p. 320. *)
Lemma laws (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R)
    (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X) alpha:
  @is_holomorphic_zero_germ R X NX hNX a alpha (@value R X NX hNX a alpha).
Proof. exact:(projT2 (cid (@holomorphic_zero_germ_exists R X NX hNX a alpha))). Qed.
End HolomorphicZeroGerm.
