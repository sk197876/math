(** Opaque interface for the smooth example
    of Federer (1969), 3.1.11, p. 223.
    The defining branches and the proved
    derivative-sequence laws are exposed; the
    polynomial witnesses remain private. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import ScalarSmoothSequenceUP FlatExponentialUP FlatExponentialConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type FlatExponentialSignature.
(** Source for [value]: the scalar function
    exp(-x^-2) for x>0, zero otherwise,
    Federer 3.1.11, p. 223. *)
Parameter value : forall R : realType, R->R.
(** Source for [laws]: the two defining
    branch laws, Federer 3.1.11, p. 223. *)
Parameter laws : forall R : realType, is_flat_exponential (@value R).
(** Source for [smooth_derivatives]: all ordinary
    derivatives exist and vanish on x<= 0,
    Federer 3.1.11, p. 223. *)
Parameter smooth_derivatives : forall R : realType,
  exists F : nat->R->R,
    is_scalar_smooth_derivative_sequence (@value R) F /\
    forall k x, x<= 0 -> F k x= 0.
End FlatExponentialSignature.

Module FlatExponential : FlatExponentialSignature.
(** Source for [value]: a proved witness
    of the branch laws in Federer
    3.1.11, p. 223. *)
Definition value (R : realType) :=
  sval (constructive_indefinite_description (@flat_exponential_exists R)).
(** Source for [laws]: the witness satisfies
    the defining values in Federer
    3.1.11, p. 223. *)
Lemma laws (R : realType) : is_flat_exponential (@value R).
Proof. exact: (svalP (constructive_indefinite_description (@flat_exponential_exists R))).1. Qed.
(** Source for [smooth_derivatives]: the private
    existence proof establishes every derivative
    law for Federer 3.1.11, p. 223. *)
Lemma smooth_derivatives (R : realType) :
  exists F : nat->R->R,
    is_scalar_smooth_derivative_sequence (@value R) F /\
    forall k x, x<= 0 -> F k x= 0.
Proof. exact: (svalP (constructive_indefinite_description (@flat_exponential_exists R))).2. Qed.
End FlatExponential.
