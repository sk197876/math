(** Federer (1969), 3.2.33, p. 270: independent
    laws for the smooth scalar function phi positive on (0,1)
    and zero elsewhere, used in the printed smooth example. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP NormRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_positive_unit_interval_bump]: the choice of
    phi in Federer 3.2.33, p. 270, first construction
    paragraph. The function is globally smooth with the actual
    recursive higher differentials, positive exactly on the open
    unit interval, and zero outside. A unit upper bound is a
    convenient harmless normalization of the permitted choice. *)
Record is_positive_unit_interval_bump (R:realType) (phi:R->R):Prop:={
  (** Source for [positive_interval_bump_bounds]: supporting nonnegative
      unit normalization of phi in Federer 3.2.33, p. 270. *)
  positive_interval_bump_bounds:forall t,0<=phi t<= 1;
  (** Source for [positive_interval_bump_positive]: phi is positive
      on exactly T= (0,1), Federer 3.2.33, p. 270. *)
  positive_interval_bump_positive:forall t,(0<phi t)= (0<t<1);
  (** Source for [positive_interval_bump_zero]: phi vanishes outside
      T, Federer 3.2.33, p. 270. *)
  positive_interval_bump_zero:forall t,t<= 0 \/1<=t ->phi t= 0;
  (** Source for [positive_interval_bump_smooth]: the global class
      infinity requirement for phi in Federer 3.2.33, p. 270. *)
  positive_interval_bump_smooth:norm_class_all_orders (scalar_absolute_value_norm R)
    (scalar_absolute_value_norm R) (fun _=>True) phi
}.
