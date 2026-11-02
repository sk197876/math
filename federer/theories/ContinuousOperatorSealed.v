(** Opaque continuous-operator space for Federer (1969), 3.1.1,
    pp. 210-211. Only its evaluation and least-bound laws are public. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousOperatorUP ContinuousOperatorConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type ContinuousOperatorSignature.
(** Source for [space]: the normed space of continuous linear maps
    in 3.1.1, pp. 210-211. *)
Parameter space : forall (R : realType) (X Y : lmodType R)
  (NX : X -> R) (NY : Y -> R), is_real_norm NX -> is_real_norm NY -> lmodType R.
(** Source for [evaluation]: linear evaluation of represented
    operators, supporting 3.1.1, pp. 210-211. *)
Parameter evaluation : forall (R : realType) (X Y : lmodType R)
  (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX) (hNY : is_real_norm NY),
  Hom (@space R X Y NX NY hNX hNY) (Hom X Y).
(** Source for [norm]: the least-bound operator norm used in
    3.1.1, pp. 210-211. *)
Parameter norm : forall (R : realType) (X Y : lmodType R)
  (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX) (hNY : is_real_norm NY),
  @space R X Y NX NY hNX hNY -> R.
(** Source for [laws]: the defining laws proved by the hidden
    witness for the operator space in 3.1.1, pp. 210-211. *)
Parameter laws : forall (R : realType) (X Y : lmodType R)
  (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX) (hNY : is_real_norm NY),
  is_continuous_operator_space NX NY (@evaluation R X Y NX NY hNX hNY)
    (@norm R X Y NX NY hNX hNY).
End ContinuousOperatorSignature.
Module ContinuousOperator : ContinuousOperatorSignature.
(** Source for [space]: private proved carrier for the operator
    space in 3.1.1, pp. 210-211. *)
Definition space (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX) (hNY : is_real_norm NY) : lmodType R :=
  @continuous_operator_carrier R X Y NX NY hNY.
(** Source for [evaluation]: private injective evaluation witness
    for 3.1.1, pp. 210-211. *)
Definition evaluation (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX) (hNY : is_real_norm NY) :
    Hom (@space R X Y NX NY hNX hNY) (Hom X Y) :=
  @continuous_operator_evaluation_witness R X Y NX NY hNY.
(** Source for [norm]: private least-bound witness supporting
    3.1.1, pp. 210-211. *)
Definition norm (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX) (hNY : is_real_norm NY) :
    @space R X Y NX NY hNX hNY -> R :=
  @continuous_operator_norm_witness R X Y NX NY hNX hNY.
(** Source for [laws]: proof of the abstract promises for the
    operator-space witness in 3.1.1, pp. 210-211. *)
Lemma laws (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX) (hNY : is_real_norm NY) :
  is_continuous_operator_space NX NY (@evaluation R X Y NX NY hNX hNY)
    (@norm R X Y NX NY hNX hNY).
Proof. exact: continuous_operator_witness_laws. Qed.
End ContinuousOperator.
