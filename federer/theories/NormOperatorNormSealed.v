(** Opaque general operator norm for Federer (1969), 3.1.1,
    pp. 209–210. The supremum witness remains private. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormOperatorNormUP NormOperatorNormConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type NormOperatorNormSignature.
(** Source for [value]: operator norm of a bounded linear map,
    Federer 3.1.1, pp. 209–210. *)
Parameter value : forall (R : realType) (X Y : lmodType R)
  (NX : X -> R) (NY : Y -> R), is_real_norm NX -> is_real_norm NY ->
  forall L : Hom X Y, norm_bounded_linear NX NY L -> R.
(** Source for [laws]: abstract least-bound specification of the
    operator norm in Federer 3.1.1, pp. 209–210. *)
Parameter laws : forall (R : realType) (X Y : lmodType R)
  (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
  (hNY : is_real_norm NY) (L : Hom X Y) (hL : norm_bounded_linear NX NY L),
  is_norm_operator_norm NX NY L (@value R X Y NX NY hNX hNY L hL).
End NormOperatorNormSignature.
Module NormOperatorNorm : NormOperatorNormSignature.
(** Source for [value]: private choice of the proved finite norm
    in Federer 3.1.1, pp. 209–210. *)
Definition value (R : realType) (X Y : lmodType R)
  (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
  (hNY : is_real_norm NY) (L : Hom X Y) (hL : norm_bounded_linear NX NY L) : R :=
  sval (constructive_indefinite_description (@norm_operator_norm_exists R X Y NX NY hNX hNY L hL)).
(** Source for [laws]: the chosen norm satisfies its intrinsic laws,
    Federer 3.1.1, pp. 209–210. *)
Lemma laws (R : realType) (X Y : lmodType R)
  (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
  (hNY : is_real_norm NY) (L : Hom X Y) (hL : norm_bounded_linear NX NY L) :
  is_norm_operator_norm NX NY L (@value R X Y NX NY hNX hNY L hL).
Proof. exact: (svalP (constructive_indefinite_description
  (@norm_operator_norm_exists R X Y NX NY hNX hNY L hL))). Qed.
End NormOperatorNorm.
