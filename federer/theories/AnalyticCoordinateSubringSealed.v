(** Federer (1969), 3.4.8(1), p. 326:
    original coordinate germ images hidden behind their
    independent membership laws. Existence, rather than
    a chosen image representation, supplies the sealed sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP AnalyticGermUP AnalyticCoordinateSubringUP
  AnalyticCoordinateSubringExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type AnalyticCoordinateGermImageSignature.
(** Source for [value]: the original coordinate image
    Q_j of 3.4.8(1), p. 326. *)
Parameter value:forall (R:realType) (X Y:lmodType R) (NX:X->R) (NY:Y->R)
  (hNX:is_real_norm NX) (hNY:is_real_norm NY) (a:X) (b:Y),
  (analytic_germ_space hNY b->analytic_germ_space hNX a)->set (analytic_germ_space hNX a).
(** Source for [laws]: the original image membership
    equation in 3.4.8(1), p. 326. *)
Parameter laws:forall (R:realType) (X Y:lmodType R) (NX:X->R) (NY:Y->R)
  (hNX:is_real_norm NX) (hNY:is_real_norm NY) (a:X) (b:Y)
  (P:analytic_germ_space hNY b->analytic_germ_space hNX a),
  is_analytic_coordinate_germ_image P (@value R X Y NX NY hNX hNY a b P).
End AnalyticCoordinateGermImageSignature.
Module AnalyticCoordinateGermImage:AnalyticCoordinateGermImageSignature.
(** Source for [value]: a hidden image from proved
    existence, supporting 3.4.8(1), p. 326. *)
Definition value (R:realType) (X Y:lmodType R) (NX:X->R) (NY:Y->R)
  (hNX:is_real_norm NX) (hNY:is_real_norm NY) (a:X) (b:Y)
  (P:analytic_germ_space hNY b->analytic_germ_space hNX a):=
  projT1 (cid (@analytic_coordinate_germ_image_exists R X Y NX NY hNX hNY a b P)).
(** Source for [laws]: the selected image satisfies
    the original membership law, 3.4.8(1), p. 326. *)
Lemma laws (R:realType) (X Y:lmodType R) (NX:X->R) (NY:Y->R)
  (hNX:is_real_norm NX) (hNY:is_real_norm NY) (a:X) (b:Y)
  (P:analytic_germ_space hNY b->analytic_germ_space hNX a):
  is_analytic_coordinate_germ_image P (@value R X Y NX NY hNX hNY a b P).
Proof. exact:(projT2 (cid (@analytic_coordinate_germ_image_exists R X Y NX NY hNX hNY a b P))). Qed.
End AnalyticCoordinateGermImage.
