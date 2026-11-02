(** Federer (1969), 3.2.31, p. 269: supporting the
    symmetric automorphism approximating a rank-deficient map.
    Specify its separate actions on a projection range and kernel
    before proving existence by a local linear combination. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom SymmetricEndomorphisms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_projection_scale_automorphism]: independent
    supporting laws for the small automorphism in Federer
    3.2.31, p. 269. It scales the projection range and
    complementary kernel by prescribed nonzero coefficients,
    with an actual inverse and symmetry. The algebraic
    supporting specification is valid over every field;
    the final measure theorem uses real Euclidean spaces. *)
Record is_projection_scale_automorphism (K:fieldType) (V:lmodType K)
    (B:V->V->K) (P:Hom V V) (a b:K) (T U:Hom V V):Prop:={
  (** Source for [projection_scale_symmetric]: symmetry of the
      approximating automorphism in 3.2.31, p. 269. *)
  projection_scale_symmetric:is_symmetric_endomorphism B (hom_as_linear T);
  (** Source for [projection_scale_left_inverse]: actual inverse
      law supporting t^-1 in 3.2.31, p. 269. *)
  projection_scale_left_inverse:cancel T U;
  (** Source for [projection_scale_right_inverse]: other inverse
      law supporting t^-1 in 3.2.31, p. 269. *)
  projection_scale_right_inverse:cancel U T;
  (** Source for [projection_scale_range]: the prescribed scale
      on the low-rank range, supporting 3.2.31, p. 269. *)
  projection_scale_range:forall x,T (P x)=a*:P x;
  (** Source for [projection_scale_kernel]: the prescribed small
      scale on the complementary kernel, supporting 3.2.31, p. 269. *)
  projection_scale_kernel:forall x,P x=0 ->T x=b*:x;
  (** Source for [projection_scale_inverse_range]: reciprocal
      scale on the range, supporting 3.2.31, p. 269. *)
  projection_scale_inverse_range:forall x,U (P x)=a^-1*:P x;
  (** Source for [projection_scale_inverse_kernel]: reciprocal
      scale on the kernel, supporting 3.2.31, p. 269. *)
  projection_scale_inverse_kernel:forall x,P x=0 ->U x=b^-1*:x
}.
