(** Federer (1969), 3.1.1, p. 209: finite limsup and liminf of the
    increment ratio. The epsilon and arbitrarily-small-neighbourhood
    laws specify the limits, including sharpness. All evaluations are
    guarded by a positive increment norm. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_increment_ratio]: the quotient of image and source
    increment lengths in Federer 3.1.1, p. 209. Limit laws use it only
    when the source increment norm is positive. *)
Definition norm_increment_ratio (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (f : X -> Y) (a h : X) :=
  NY (f (a+h)-f a)/NX h.

(** Source for [is_norm_ratio_limsup]: the upper limit in Federer
    3.1.1, p. 209, specified by eventual upper estimates and values
    arbitrarily close from below in every punctured neighbourhood. *)
Record is_norm_ratio_limsup (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (A : X -> Prop)
    (f : X -> Y) (a : X) (l : R) : Prop := {
  (** Source for [norm_ratio_eventual_upper]: eventual upper estimate
      in the limsup formula of Federer 3.1.1, p. 209. *)
  norm_ratio_eventual_upper : forall e : R, 0 < e -> exists d : R,
    0 < d /\ forall h, A (a+h) -> 0 < NX h < d ->
      norm_increment_ratio NX NY f a h < l+e;
  (** Source for [norm_ratio_sharp_upper]: sharpness of that upper
      estimate in every punctured neighbourhood, Federer 3.1.1, p. 209. *)
  norm_ratio_sharp_upper : forall e d : R, 0 < e -> 0 < d -> exists h,
    A (a+h) /\ 0 < NX h < d /\ l-e < norm_increment_ratio NX NY f a h
}.

(** Source for [is_norm_ratio_liminf]: the lower limit in Federer
    3.1.1, p. 209, specified by eventual lower estimates and values
    arbitrarily close from above in every punctured neighbourhood. *)
Record is_norm_ratio_liminf (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (A : X -> Prop)
    (f : X -> Y) (a : X) (l : R) : Prop := {
  (** Source for [norm_ratio_eventual_lower]: eventual lower estimate
      in the liminf formula of Federer 3.1.1, p. 209. *)
  norm_ratio_eventual_lower : forall e : R, 0 < e -> exists d : R,
    0 < d /\ forall h, A (a+h) -> 0 < NX h < d ->
      l-e < norm_increment_ratio NX NY f a h;
  (** Source for [norm_ratio_sharp_lower]: sharpness of that lower
      estimate in every punctured neighbourhood, Federer 3.1.1, p. 209. *)
  norm_ratio_sharp_lower : forall e d : R, 0 < e -> 0 < d -> exists h,
    A (a+h) /\ 0 < NX h < d /\ norm_increment_ratio NX NY f a h < l+e
}.
