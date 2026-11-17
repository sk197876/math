(** Federer (1969), 3.4.8(2), p. 326:
    the original rotated ideal image hidden behind its
    independent membership law. Choice supplies only a
    witness of the proved existence theorem. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
From Federer Require Import AnalyticRotatedIdealUP AnalyticRotatedIdealExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type AnalyticIdealImageSignature.
(** Source for [value]: the original image I_g,
    supporting 3.4.8(2), p. 326. *)
Parameter value:forall (A B:comNzRingType),{rmorphism A->B}->set A->set B.
(** Source for [laws]: the independent original membership
    equation for I_g, 3.4.8(2), p. 326. *)
Parameter laws:forall (A B:comNzRingType) (M:{rmorphism A->B}) (I:set A),
  is_analytic_ideal_image M I (@value A B M I).
End AnalyticIdealImageSignature.
Module AnalyticIdealImage:AnalyticIdealImageSignature.
(** Source for [value]: the hidden image witness from
    proved existence, supporting 3.4.8(2), p. 326. *)
Definition value (A B:comNzRingType) (M:{rmorphism A->B}) (I:set A):=
  projT1 (cid (@analytic_ideal_image_exists A B M I)).
(** Source for [laws]: the selected image satisfies
    the independent original equation, 3.4.8(2), p. 326. *)
Lemma laws (A B:comNzRingType) (M:{rmorphism A->B}) (I:set A):
  is_analytic_ideal_image M I (@value A B M I).
Proof. exact:(projT2 (cid (@analytic_ideal_image_exists A B M I))). Qed.
End AnalyticIdealImage.
