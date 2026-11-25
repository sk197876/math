(** Federer (1969), 3.1.23, pp. 236–237: smooth
    radial cutoff, equal to one through radius t and zero
    beyond radius one, with a finite differential bound. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_norm_annular_cutoff]: laws needed of
    u(x)= gamma(|x|) in Federer 3.1.23, pp. 236–237,
    before spatial scaling by r. Smoothness and a finite
    differential bound are proved by the implementation; the
    specification postulates no cutoff or differentiability axiom. *)
Record is_norm_annular_cutoff (R:realType) (X:lmodType R)
    (N:X->R) (hN:is_real_norm N) t (u:X->R^o) C : Prop := {
  (** Source for [annular_cutoff_range]: 0<=u<=1, Federer
      3.1.23, pp. 236–237. *)
  annular_cutoff_range:forall x,0<=u x<=1;
  (** Source for [annular_cutoff_inner]: u= 1 through the inner
      radius t, Federer 3.1.23, pp. 236–237. *)
  annular_cutoff_inner:forall x,N x<=t -> u x= 1;
  (** Source for [annular_cutoff_outer]: u= 0 at and beyond the
      unit radius, Federer 3.1.23, p. 237. *)
  annular_cutoff_outer:forall x,1<=N x -> u x= 0;
  (** Source for [annular_cutoff_radial]: the cutoff depends only
      on the norm, Federer 3.1.23, p. 237. *)
  annular_cutoff_radial:forall x y,N x= N y -> u x= u y;
  (** Source for [annular_cutoff_smooth]: class infinity of u,
      Federer 3.1.23, p. 237. *)
  annular_cutoff_smooth:norm_class_all_orders hN (scalar_absolute_value_norm R)
    (fun _=>True) u;
  (** Source for [annular_cutoff_bound_positive]: a positive finite
      bound for the differential, supporting Lip(gamma) in Federer
      3.1.23, pp. 236–237. *)
  annular_cutoff_bound_positive:0<C;
  (** Source for [annular_cutoff_differential_bound]: the unscaled
      differential estimate for u, used after spatial scaling in
      Federer 3.1.23, p. 237. *)
  annular_cutoff_differential_bound:forall x (L:Hom X R^o),
    has_norm_differential N (fun s:R^o=>`|s|) (fun _=>True) u x L ->
    forall v,`|L v|<=C*N v
}.
