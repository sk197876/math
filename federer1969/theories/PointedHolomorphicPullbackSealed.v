(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),(5), pp. 326, 328:
    pointed coordinate pullbacks selected from proved existence
    and hidden behind their independent representative laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed HolomorphicAtUP HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP NormAnalyticUP HolomorphicGermUP
  PointedHolomorphicPullbackUP PointedHolomorphicPullbackExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type PointedHolomorphicPullbackSignature.
(** Source for [map]: the original pointed coordinate
    map on germs, supporting 3.4.8(1),(5), pp. 326, 328. *)
Parameter map:forall (R:realType) (X Y:lmodType (ComplexScalars.C R)) (NX:X->R) (NY:Y->R)
  (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY) (A:set X) (u:X->Y) (a:X) (b:Y),
  @is_holomorphic_at R X Y NX NY hNX hNY A u a ->u a=b ->
  holomorphic_germ_space hNY b->holomorphic_germ_space hNX a.
(** Source for [laws]: every original representative
    equation, supporting 3.4.8(1),(5), pp. 326, 328. *)
Parameter laws:forall (R:realType) (X Y:lmodType (ComplexScalars.C R)) (NX:X->R) (NY:Y->R)
  (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY) (A:set X) (u:X->Y) (a:X) (b:Y)
  (hu:@is_holomorphic_at R X Y NX NY hNX hNY A u a) (hab:u a=b),
  is_pointed_holomorphic_germ_pullback u (@map R X Y NX NY hNX hNY A u a b hu hab).
End PointedHolomorphicPullbackSignature.
Module PointedHolomorphicPullback:PointedHolomorphicPullbackSignature.
(** Source for [map]: a private choice from proved
    existence, supporting 3.4.8(1),(5), pp. 326, 328. *)
Definition map (R:realType) (X Y:lmodType (ComplexScalars.C R)) (NX:X->R) (NY:Y->R)
  (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY) (A:set X) (u:X->Y) (a:X) (b:Y)
  (hu:@is_holomorphic_at R X Y NX NY hNX hNY A u a) (hab:u a=b):=
  projT1 (cid (@pointed_holomorphic_germ_pullback_exists R X Y NX NY hNX hNY A u a b hu hab)).
(** Source for [laws]: the hidden witness satisfies
    the independent equations of 3.4.8(1),(5), pp. 326, 328. *)
Lemma laws (R:realType) (X Y:lmodType (ComplexScalars.C R)) (NX:X->R) (NY:Y->R)
  (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY) (A:set X) (u:X->Y) (a:X) (b:Y)
  (hu:@is_holomorphic_at R X Y NX NY hNX hNY A u a) (hab:u a=b):
  is_pointed_holomorphic_germ_pullback u (@map R X Y NX NY hNX hNY A u a b hu hab).
Proof.
exact:(projT2 (cid (@pointed_holomorphic_germ_pullback_exists R X Y NX NY hNX hNY A u a b hu hab))).
Qed.
End PointedHolomorphicPullback.
