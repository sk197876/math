(** Federer (1969), 3.1.1, pp. 210-211: the normed space of
    continuous linear maps, in which the differential takes values.
    Its carrier, evaluation and norm are specified by laws. A
    construction must prove these laws; no project axiom is added. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom NormDifferentialUP NormOperatorNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_continuous_operator_space]: the space of all
    continuous linear maps in 3.1.1, pp. 210-211. Evaluation identifies
    its elements exactly with the bounded linear maps, and the norm
    is their least nonnegative homogeneous evaluation bound. *)
Record is_continuous_operator_space (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (Z : lmodType R)
    (evaluation : Hom Z (Hom X Y)) (ZN : Z -> R) : Prop := {
  (** Source for [continuous_operator_injective]: operators are
      identified by their values, 3.1.1, pp. 210-211. *)
  continuous_operator_injective : injective evaluation;
  (** Source for [continuous_operator_bounded]: every represented
      operator is continuous, 3.1.1, pp. 210-211. *)
  continuous_operator_bounded : forall z,
    norm_bounded_linear NX NY (evaluation z);
  (** Source for [continuous_operator_surjective]: the space contains
      all continuous linear maps, 3.1.1, pp. 210-211. *)
  continuous_operator_surjective : forall L : Hom X Y,
    norm_bounded_linear NX NY L -> exists z, evaluation z=L;
  (** Source for [continuous_operator_norm_laws]: the operator norm
      used for continuity and Borel measurability of Df in
      3.1.1, pp. 210-211. *)
  continuous_operator_norm_laws : forall z,
    is_norm_operator_norm NX NY (evaluation z) (ZN z)
}.
