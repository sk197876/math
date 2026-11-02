(** Opaque derivative-sequence composition for
    Federer (1969), 3.1.11, p. 223.
    Only the proved existence law is exposed;
    the finite expression representation is private. *)
From mathcomp Require Import all_boot reals.
From Federer Require Import ScalarSmoothSequenceUP ScalarSmoothCompositionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type ScalarSmoothCompositionSignature.
(** Source for [derivatives]: composing two
    smooth scalar functions supplies a smooth
    derivative sequence, as used in Federer
    3.1.11, p. 223. *)
Parameter derivatives : forall (R : realType) (f g : R->R) (F G : nat->R->R),
  is_scalar_smooth_derivative_sequence f F ->
  is_scalar_smooth_derivative_sequence g G ->
  exists H : nat->R->R,
    is_scalar_smooth_derivative_sequence (fun x=>f (g x)) H.
End ScalarSmoothCompositionSignature.

Module ScalarSmoothComposition : ScalarSmoothCompositionSignature.
(** Source for [derivatives]: the finite
    expression induction proves the composition
    law used in Federer 3.1.11, p. 223. *)
Theorem derivatives (R : realType) (f g : R->R) (F G : nat->R->R) :
  is_scalar_smooth_derivative_sequence f F ->
  is_scalar_smooth_derivative_sequence g G ->
  exists H : nat->R->R,
    is_scalar_smooth_derivative_sequence (fun x=>f (g x)) H.
Proof. exact: scalar_smooth_composition_derivatives_exists. Qed.
End ScalarSmoothComposition.
