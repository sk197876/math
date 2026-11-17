(** Federer (1969), 3.4.12, p. 339: specify the original
    directional order before proving complex division or preparation.
    The opaque complex germ forms are its actual derivatives. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP SymmetricForms
  HolomorphicGermUP HolomorphicGermFormsUP HolomorphicGermFormsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_complex_weierstrass_regular_germ]: the original
    positive order k, vanishing lower directional derivatives and
    nonzero kth derivative of 3.4.6, p. 321, over the
    complex field as required by 3.4.12, p. 339. *)
Definition is_complex_weierstrass_regular_germ (R:realType)
    (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX)
    (alpha:holomorphic_germ_space (complex_norm_real hNX) (0:X)) k (v:X):Prop:=
  (0<k)%N /\
  (forall i,(i<k)%N ->@HolomorphicGermForms.value R X NX hNX 0 i alpha [tuple v | j<i]=0) /\
  @HolomorphicGermForms.value R X NX hNX 0 k alpha [tuple v | j<k]<>0.
Arguments is_complex_weierstrass_regular_germ {R X NX} hNX alpha k v.
