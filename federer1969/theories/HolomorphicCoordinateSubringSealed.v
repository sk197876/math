(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1), p. 326:
    original coordinate germ images hidden behind their
    independent membership laws. Existence, rather than
    a chosen image representation, supplies the sealed sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed HolomorphicAtUP RealNormUP HolomorphicGermUP HolomorphicCoordinateSubringUP
  HolomorphicCoordinateSubringExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type HolomorphicCoordinateGermImageSignature.
(** Source for [value]: the original coordinate image
    Q_j of 3.4.8(1), p. 326. *)
Parameter value:forall (R:realType) (X Y:lmodType (ComplexScalars.C R)) (NX:X->R) (NY:Y->R)
  (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY) (a:X) (b:Y),
  (holomorphic_germ_space hNY b->holomorphic_germ_space hNX a)->set (holomorphic_germ_space hNX a).
(** Source for [laws]: the original image membership
    equation in 3.4.8(1), p. 326. *)
Parameter laws:forall (R:realType) (X Y:lmodType (ComplexScalars.C R)) (NX:X->R) (NY:Y->R)
  (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY) (a:X) (b:Y)
  (P:holomorphic_germ_space hNY b->holomorphic_germ_space hNX a),
  is_holomorphic_coordinate_germ_image P (@value R X Y NX NY hNX hNY a b P).
End HolomorphicCoordinateGermImageSignature.
Module HolomorphicCoordinateGermImage:HolomorphicCoordinateGermImageSignature.
(** Source for [value]: a hidden image from proved
    existence, supporting 3.4.8(1), p. 326. *)
Definition value (R:realType) (X Y:lmodType (ComplexScalars.C R)) (NX:X->R) (NY:Y->R)
  (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY) (a:X) (b:Y)
  (P:holomorphic_germ_space hNY b->holomorphic_germ_space hNX a):=
  projT1 (cid (@holomorphic_coordinate_germ_image_exists R X Y NX NY hNX hNY a b P)).
(** Source for [laws]: the selected image satisfies
    the original membership law, 3.4.8(1), p. 326. *)
Lemma laws (R:realType) (X Y:lmodType (ComplexScalars.C R)) (NX:X->R) (NY:Y->R)
  (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY) (a:X) (b:Y)
  (P:holomorphic_germ_space hNY b->holomorphic_germ_space hNX a):
  is_holomorphic_coordinate_germ_image P (@value R X Y NX NY hNX hNY a b P).
Proof. exact:(projT2 (cid (@holomorphic_coordinate_germ_image_exists R X Y NX NY hNX hNY a b P))). Qed.
End HolomorphicCoordinateGermImage.
