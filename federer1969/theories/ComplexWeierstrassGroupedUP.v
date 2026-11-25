(** Federer (1969), 3.4.12, p. 339: specify the original
    complex double series through its actual homogeneous Taylor
    coefficients. No existence or division assertion enters these laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom ScalarRestriction ComplexScalarSealed ComplexNormUP
  SymmetricForms HomogeneousPolynomialFunctions HolomorphicGermUP
  HolomorphicGermFormsUP HolomorphicGermFormsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_complex_weierstrass_grouped_germ]: the finite
    total-degree grouping of 3.4.6, p. 323, with the original
    complex derivative forms as required by 3.4.12, p. 339. *)
Definition is_complex_weierstrass_grouped_germ (R:realType)
    (X K:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX)
    (xi:Hom X (ComplexScalars.C R)^o) (projection:Hom X K)
    (q:nat->nat->K->ComplexScalars.C R)
    (alpha:holomorphic_germ_space (complex_norm_real hNX) (0:X)):Prop:=
  forall m x,(\sum_(i<m.+1) (xi x)^+i*q i (m-i)%N (projection x))=
    sform_polynomial_value (@HolomorphicGermForms.value R X NX hNX 0 m alpha) x.
Arguments is_complex_weierstrass_grouped_germ {R X K NX} hNX xi projection q alpha.
