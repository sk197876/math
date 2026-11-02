(** Federer (1969), 3.1.13, p. 224:
    abstract laws of the smooth radial function
    used to build the partition of unity. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import NormBoundedBilinearUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_squared_bilinear_form]:
    the Euclidean squared norm is a continuous
    quadratic polynomial, supporting the construction
    of mu in Federer 3.1.13, p. 224.
    This auxiliary specification also applies to
    any norm coming from an inner product. *)
Definition norm_squared_bilinear_form (R : realType) (X : lmodType R)
    (N : X->R) (B : X->X->R^o) :=
  norm_bounded_bilinear N N (fun t : R^o=>`|t|) B /\
  forall x, B x x=(N x)^+2.

(** Source for [is_norm_unit_bump]:
    the radial cutoff mu in Federer 3.1.13,
    p. 224: values between zero and
    one, equal to one on the closed
    unit ball and zero outside the ball
    of radius two. Smoothness is specified
    separately using the actual higher differential. *)
Record is_norm_unit_bump (R : realType) (X : Type)
    (N : X->R) (mu : X->R) : Prop := {
  (** Source for [norm_unit_bump_range]:
      the range of mu is contained in
      [0,1], Federer 3.1.13, p. 224. *)
  norm_unit_bump_range : forall x, 0<=mu x<=1;
  (** Source for [norm_unit_bump_inner]:
      mu equals one on the unit ball,
      Federer 3.1.13, p. 224. *)
  norm_unit_bump_inner : forall x, N x<=1 -> mu x= 1;
  (** Source for [norm_unit_bump_outer]:
      mu vanishes at norm at least two,
      Federer 3.1.13, p. 224. *)
  norm_unit_bump_outer : forall x, 2<=N x -> mu x=0;
  (** Source for [norm_unit_bump_radial]:
      mu depends only on the norm,
      Federer 3.1.13, p. 224. *)
  norm_unit_bump_radial : forall x y, N x=N y -> mu x=mu y
}.

(** Source for [is_scalar_radial_cutoff]:
    the scalar map gamma chosen in Federer
    3.1.13, p. 224. Its
    plateau at one includes all negative arguments,
    even though norms themselves are nonnegative. *)
Record is_scalar_radial_cutoff (R : realType) (gamma : R->R) : Prop := {
  (** Source for [scalar_radial_cutoff_range]:
      gamma has range [0,1], Federer 3.1.13, p. 224. *)
  scalar_radial_cutoff_range : forall t, 0<=gamma t<=1;
  (** Source for [scalar_radial_cutoff_lower]:
      gamma(t)= 1 for t<=1, Federer 3.1.13, p. 224. *)
  scalar_radial_cutoff_lower : forall t, t<=1 -> gamma t= 1;
  (** Source for [scalar_radial_cutoff_upper]:
      gamma(t)=0 for t>=2, Federer 3.1.13, p. 224. *)
  scalar_radial_cutoff_upper : forall t, 2<=t -> gamma t=0
}.
