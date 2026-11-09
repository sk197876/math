(** Federer (1969), 3.3.19, p. 302: independent laws of the
    level counts and radii. Index j denotes book level j+3,
    with the auxiliary unit root at j= 0. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [is_factorial_disc_scales]: the initial unit
    disc and successive subdivisions by 4,5,... in 3.3.19,
    p. 302. Factorial formulas and shrinking are conclusions. *)
Record is_factorial_disc_scales (R:realType) (N:nat->nat) (rho:nat->R):Prop:={
  (** Source for [factorial_disc_count_root]: the auxiliary
      unit root preceding G_4, 3.3.19, p. 302. *)
  factorial_disc_count_root:N 0%N= 1%N;
  (** Source for [factorial_disc_count_step]: subdivision
      into n children at book level n, 3.3.19, p. 302. *)
  factorial_disc_count_step:forall j,N j.+1=((j+4)*N j)%N;
  (** Source for [factorial_disc_radius_root]: radius one
      for the original root disc, 3.3.19, p. 302. *)
  factorial_disc_radius_root:rho 0%N= 1;
  (** Source for [factorial_disc_radius_step]: child radius
      r/n, exactly as in 3.3.19, p. 302. *)
  factorial_disc_radius_step:forall j,rho j.+1=rho j/(j+4)%:R
}.
