(** Federer (1969), 3.1.23, p. 237: the scaled
    cutoff u(x)=gamma(|x-b|/r), specified by the laws used
    in the supported graph correction. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_scaled_annular_cutoff]: the range, plateaus,
    smoothness and differential estimate for u in Federer
    3.1.23, p. 237. C is a finite constant
    independent of the spatial radius r and the centre b. *)
Record is_scaled_annular_cutoff (R:realType) (X:lmodType R)
    (N:X->R) (hN:is_real_norm N) b t r (w:X->R^o) C : Prop := {
  (** Source for [scaled_cutoff_range]: 0<=u<=1, Federer
      3.1.23, p. 237. *)
  scaled_cutoff_range:forall x,0<=w x<=1;
  (** Source for [scaled_cutoff_inner]: u=1 in the inner
      radius-tr ball, Federer 3.1.23, p. 237. *)
  scaled_cutoff_inner:forall x,N (x-b)<=t*r -> w x= 1;
  (** Source for [scaled_cutoff_outer]: u=0 outside the open
      radius-r ball, Federer 3.1.23, p. 237. *)
  scaled_cutoff_outer:forall x,r<=N (x-b) -> w x= 0;
  (** Source for [scaled_cutoff_smooth]: u is smooth on the
      whole ambient space, Federer 3.1.23, p. 237. *)
  scaled_cutoff_smooth:norm_class_all_orders hN (scalar_absolute_value_norm R)
    (fun _=>True) w;
  (** Source for [scaled_cutoff_differential_bound]: the derivative
      bound C/r used in the estimate for Df-id, Federer
      3.1.23, p. 237. *)
  scaled_cutoff_differential_bound:forall x (L:Hom X R^o),
    has_norm_differential N (fun s:R^o=>`|s|) (fun _=>True) w x L ->
    forall v,`|L v|<=(C/r)*N v
}.
