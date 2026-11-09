(** Federer (1969), 3.4.6(2), p. 322: the actual
    split into a distinguished line and the kernel of a
    bounded scalar functional. The laws precede existence
    and do not select a kernel model or coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_weierstrass_transverse_space]: inclusion
    identifies the supplied transverse space with ker(xi),
    and the projection represents eta(x)=x-xi(x)v, as used
    in 3.4.6, p. 322. Both maps are bounded
    and the inclusion preserves the original norm. *)
Record is_weierstrass_transverse_space (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (v:X) (xi:Hom X R^o)
    (inclusion:Hom K X) (projection:Hom X K):Prop:={
  (** Source for [weierstrass_transverse_functional_value]: the
      original functional satisfies xi(v)=1, 3.4.6(2), p. 322. *)
  weierstrass_transverse_functional_value:xi v= 1;
  (** Source for [weierstrass_transverse_kernel]: every included
      transverse vector belongs to ker(xi), 3.4.6, p. 322. *)
  weierstrass_transverse_kernel:forall z,xi (inclusion z)=0;
  (** Source for [weierstrass_transverse_projection_equation]: the
      actual projection has exactly the printed eta formula,
      3.4.6, p. 322. *)
  weierstrass_transverse_projection_equation:forall x,inclusion (projection x)=x-(xi x)*:v;
  (** Source for [weierstrass_transverse_left_inverse]: the
      inclusion and projection identify the actual kernel,
      3.4.6, p. 322. *)
  weierstrass_transverse_left_inverse:forall z,projection (inclusion z)=z;
  (** Source for [weierstrass_transverse_inclusion_norm]: the
      original kernel has its inherited norm, supporting
      the coefficient estimates in 3.4.6, pp. 322–323. *)
  weierstrass_transverse_inclusion_norm:forall z,NX (inclusion z)=NK z;
  (** Source for [weierstrass_transverse_inclusion_bounded]: actual
      inclusion is bounded for the inherited norm, supporting
      the analytic series in 3.4.6, pp. 322–323. *)
  weierstrass_transverse_inclusion_bounded:norm_bounded_linear NK NX inclusion;
  (** Source for [weierstrass_transverse_projection_bounded]: the
      original eta map is bounded by the norm and the
      continuous functional, supporting 3.4.6, pp. 322–323. *)
  weierstrass_transverse_projection_bounded:norm_bounded_linear NX NK projection
}.
