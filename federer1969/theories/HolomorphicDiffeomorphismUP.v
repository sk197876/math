(** Federer (1969), 3.4.12, p. 339:
    a holomorphic diffeomorphism has an actual holomorphic
    inverse between its original open domain and image.
    These independent laws contain no manifold or dimension conclusion. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed RealNormUP HolomorphicUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_holomorphic_diffeomorphism]: the original
    local holomorphic change of coordinates in 3.4.12,
    p. 339. Openness follows from analyticity;
    both maps and their actual inverse laws are retained. *)
Record is_holomorphic_diffeomorphism (R:realType)
    (X:lmodType (ComplexScalars.C R)) (NX:X->R)
    (hNX:is_real_norm (fun x:restricted_space (ComplexScalars.embed R) X=>NX x))
    (A B:X->Prop) (f g:X->X):Prop:={
  (** Source for [holomorphic_diffeomorphism_forward]: the original
      forward holomorphic map in 3.4.12, p. 339. *)
  holomorphic_diffeomorphism_forward:is_holomorphic hNX hNX A f;
  (** Source for [holomorphic_diffeomorphism_inverse]: its original
      holomorphic inverse in 3.4.12, p. 339. *)
  holomorphic_diffeomorphism_inverse:is_holomorphic hNX hNX B g;
  (** Source for [holomorphic_diffeomorphism_maps]: the original
      domain maps into the stated image, 3.4.12, p. 339. *)
  holomorphic_diffeomorphism_maps:forall x,A x ->B (f x);
  (** Source for [holomorphic_diffeomorphism_inverse_maps]: the inverse
      maps into the original domain, 3.4.12, p. 339. *)
  holomorphic_diffeomorphism_inverse_maps:forall y,B y ->A (g y);
  (** Source for [holomorphic_diffeomorphism_left_inverse]: the original
      domain inverse identity, 3.4.12, p. 339. *)
  holomorphic_diffeomorphism_left_inverse:forall x,A x ->g (f x)=x;
  (** Source for [holomorphic_diffeomorphism_right_inverse]: the original
      image inverse identity, 3.4.12, p. 339. *)
  holomorphic_diffeomorphism_right_inverse:forall y,B y ->f (g y)=y
}.
