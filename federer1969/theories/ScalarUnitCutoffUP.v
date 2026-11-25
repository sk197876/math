(** Federer (1969), 3.1.11, p. 223:
    intrinsic laws of a scalar unit cutoff,
    before choosing the printed smooth witness. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_scalar_unit_cutoff]:
    the nonincreasing function g in Federer
    3.1.11, p. 223, takes values
    between zero and one, is one on
    x<= 0, and zero on x>= 1. *)
Record is_scalar_unit_cutoff (R : realType) (g : R->R) : Prop := {
  (** Source for [scalar_unit_cutoff_lower]:
      the cutoff equals one before zero,
      Federer 3.1.11, p. 223. *)
  scalar_unit_cutoff_lower : forall x, x<= 0 -> g x= 1;
  (** Source for [scalar_unit_cutoff_upper]:
      the cutoff equals zero after one,
      Federer 3.1.11, p. 223. *)
  scalar_unit_cutoff_upper : forall x, 1<=x -> g x= 0;
  (** Source for [scalar_unit_cutoff_nonincreasing]:
      the cutoff is nonincreasing, Federer
      3.1.11, p. 223. *)
  scalar_unit_cutoff_nonincreasing : forall x y, x<=y -> g y<=g x;
  (** Source for [scalar_unit_cutoff_bounds]:
      the cutoff ranges from zero to one,
      supporting its use in 3.1.13,
      p. 224, from 3.1.11, p. 223. *)
  scalar_unit_cutoff_bounds : forall x, 0<=g x<= 1
}.
