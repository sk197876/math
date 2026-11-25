(** Federer (1969), 3.4.8(10), p. 331:
    the auxiliary delta saturation behind its
    proved independent membership law. Its
    implementation is hidden from later ideal
    and analytic arguments. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealSaturationUP CommutativeIdealSaturationExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type CommutativeIdealSaturationSignature.
(** Source for [value]: the auxiliary original
    power-membership set supporting 3.4.8(10), p. 331. *)
Parameter value:forall (A:comNzRingType) (I:set A) (delta:A),set A.
(** Source for [laws]: exact original delta-power
    membership, supporting 3.4.8(10), p. 331. *)
Parameter laws:forall (A:comNzRingType) (I:set A) (delta:A),
  is_commutative_ideal_saturation I delta (@value A I delta).
End CommutativeIdealSaturationSignature.
Module CommutativeIdealSaturation:CommutativeIdealSaturationSignature.
(** Source for [value]: a hidden choice from
    proved power-membership existence, supporting
    3.4.8(10), p. 331. *)
Definition value (A:comNzRingType) (I:set A) (delta:A):set A:=
  projT1 (cid (@commutative_ideal_saturation_exists A I delta)).
(** Source for [laws]: the hidden choice satisfies
    the independent original membership law,
    supporting 3.4.8(10), p. 331. *)
Lemma laws (A:comNzRingType) (I:set A) (delta:A):
  is_commutative_ideal_saturation I delta (@value A I delta).
Proof. exact:projT2 (cid (@commutative_ideal_saturation_exists A I delta)). Qed.
End CommutativeIdealSaturation.
