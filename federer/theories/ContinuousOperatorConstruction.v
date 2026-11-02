(** Private proved operator-space witness supporting Federer (1969),
    3.1.1, pp. 210-211. Bounded maps form a linear subspace of Hom;
    the already sealed operator norm supplies their least-bound norm. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier RealNormUP
  NormDifferentialUP NormDifferentialLinear NormOperatorNorm
  ContinuousOperatorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section Witness.
Variable R : realType.
Variables X Y : lmodType R.
Variable NX : X -> R.
Variable NY : Y -> R.
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.

(** Source for [continuous_operator_subspace]: closure of the
    continuous linear maps under the vector operations, supporting
    the operator space in 3.1.1, pp. 210-211. *)
Definition continuous_operator_subspace : subspace (Hom X Y) :=
  @Subspace R (Hom X Y) (norm_bounded_linear NX NY)
    (@norm_bounded_linear_zero R X Y NX NY hNY)
    (@norm_bounded_linear_add R X Y NX NY hNY)
    (fun c L => @norm_bounded_linear_scale R X Y NX NY hNY L c).

(** Source for [continuous_operator_carrier]: the private space
    witnessing the abstract specification for 3.1.1, pp. 210-211. *)
Definition continuous_operator_carrier : lmodType R :=
  [the lmodType R of subspace_space continuous_operator_subspace].

(** Source for [continuous_operator_evaluation_witness]: the
    injective linear evaluation of the operator-space witness,
    supporting 3.1.1, pp. 210-211. *)
Definition continuous_operator_evaluation_witness :
    Hom continuous_operator_carrier (Hom X Y) :=
  hom_of_linear (subspace_inclusion continuous_operator_subspace).

(** Source for [continuous_operator_norm_witness]: the existing
    sealed least-bound norm on each represented operator, supporting
    the operator-space norm in 3.1.1, pp. 210-211. *)
Definition continuous_operator_norm_witness (z : continuous_operator_carrier) : R :=
  norm_operator_norm hNX hNY (subspace_valP z).

(** Source for [continuous_operator_witness_laws]: verification
    that the constructed space has exactly the specified operators
    and their norms, supporting 3.1.1, pp. 210-211. *)
Theorem continuous_operator_witness_laws :
  is_continuous_operator_space NX NY continuous_operator_evaluation_witness
    continuous_operator_norm_witness.
Proof.
constructor.
- exact: subspace_val_injective.
- exact: subspace_valP.
- move=> L hL; exists (@subspace_lift R (Hom X Y) continuous_operator_subspace L hL).
  by [].
- move=> z; exact: norm_operator_norm_specification.
Qed.
End Witness.
