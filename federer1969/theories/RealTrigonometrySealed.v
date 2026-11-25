(** Opaque elementary sine, cosine and principal inverse
    for Federer (1969), 3.2.7, p. 246.
    Only proved scalar laws cross this boundary. *)
From mathcomp Require Import all_boot boolp reals.
From Federer Require Import RealTrigonometryUP RealTrigonometryConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type RealTrigonometrySignature.
(** Source for [sine]: the scalar sine of the first and
    third examples in Federer 3.2.7, p. 246, exposed abstractly. *)
Parameter sine:forall R:realType,R->R.
(** Source for [cosine]: the actual derivative of sine,
    scalar background for Federer 3.2.7, p. 246. *)
Parameter cosine:forall R:realType,R->R.
(** Source for [arcsine]: principal inverse branch supporting
    the multiplicity calculation in Federer 3.2.7, p. 246. *)
Parameter arcsine:forall R:realType,R->R.
(** Source for [half_period]: pi in the elementary sine
    examples of Federer 3.2.7, p. 246. *)
Parameter half_period:forall R:realType,R.
(** Source for [laws]: proved abstract scalar laws supporting
    both sine examples in Federer 3.2.7, p. 246. *)
Parameter laws:forall R:realType,is_real_trigonometric_system
  (@sine R) (@cosine R) (@arcsine R) (@half_period R).
End RealTrigonometrySignature.
Module RealTrigonometry:RealTrigonometrySignature.
(** Source for [sine]: hidden witness selected from proved
    trigonometric existence for Federer 3.2.7, p. 246. *)
Definition sine (R:realType):=projT1 (cid (@real_trigonometric_system_exists R)).
(** Source for [cosine]: hidden derivative witness supporting
    the sine examples in Federer 3.2.7, p. 246. *)
Definition cosine (R:realType):=projT1 (cid (projT2 (cid (@real_trigonometric_system_exists R)))).
(** Source for [arcsine]: hidden inverse-branch witness supporting
    the first example in Federer 3.2.7, p. 246. *)
Definition arcsine (R:realType):=projT1 (cid (projT2 (cid
  (projT2 (cid (@real_trigonometric_system_exists R)))))).
(** Source for [half_period]: hidden period witness for
    the sine examples in Federer 3.2.7, p. 246. *)
Definition half_period (R:realType):=projT1 (cid (projT2 (cid
  (projT2 (cid (projT2 (cid (@real_trigonometric_system_exists R)))))))).
(** Source for [laws]: the selected trigonometric witnesses
    satisfy the abstract laws supporting Federer 3.2.7, p. 246. *)
Lemma laws (R:realType):is_real_trigonometric_system
  (@sine R) (@cosine R) (@arcsine R) (@half_period R).
Proof.
exact (projT2 (cid (projT2 (cid (projT2 (cid
  (projT2 (cid (@real_trigonometric_system_exists R))))))))).
Qed.
End RealTrigonometry.
