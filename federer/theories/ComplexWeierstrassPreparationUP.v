(** Federer (1969), 3.4.12, p. 339: specify original
    complex preparation by its germ equation, nonzero multiplier
    and monic transverse expression, before existence and sealing. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm
  HolomorphicUP HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Preparation.
Variable R:realType.
Variables X K:lmodType (ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation KR:=(restricted_space (ComplexScalars.embed R) K).
Local Notation C:=(ComplexScalars.C R).
Variables (NX:XR->R) (NK:KR->R).
Variables (hNX:is_real_norm NX) (hNK:is_real_norm NK).

(** Source for [is_complex_weierstrass_polynomial_germ]: the original
    monic degree-k polynomial in xi with holomorphic transverse
    coefficient germs vanishing at zero, extending 3.4.6(2),
    p. 322, under 3.4.12, p. 339. *)
Definition is_complex_weierstrass_polynomial_germ (xi:Hom X C^o) (projection:Hom X K) k
    (W:@holomorphic_germ_ring R X NX hNX 0)
    (Wi:'I_k->@holomorphic_germ_ring R K NK hNK 0):Prop:=
  exists w:@holomorphic_representative_type R X NX hNX 0,holomorphic_germ w=W /\
  exists coefficients:'I_k->@holomorphic_representative_type R K NK hNK 0,
    (forall i,holomorphic_germ (coefficients i)=Wi i) /\
    (forall i,holomorphic_representative_value (coefficients i) 0=0) /\
    exists U:set X,U 0 /\
      is_holomorphic hNX (@complex_modulus_real_norm R) U (holomorphic_representative_value w) /\
      forall x,U x ->holomorphic_representative_value w x=(xi x)^+k+
        \sum_(i<k) (xi x)^+i*holomorphic_representative_value (coefficients i) (projection x).

(** Source for [is_complex_weierstrass_preparation]: the exact original
    complex germ equation, Q(0) nonzero and all Wi(0)=0,
    extending 3.4.6(2), p. 322, under 3.4.12, p. 339.
    No existence or uniqueness assertion enters these independent laws. *)
Record is_complex_weierstrass_preparation (xi:Hom X C^o) (projection:Hom X K) k
    (Phi Q W:@holomorphic_germ_ring R X NX hNX 0)
    (Wi:'I_k->@holomorphic_germ_ring R K NK hNK 0):Prop:={
  (** Source for [complex_weierstrass_preparation_identity]: the original
      equation Q Phi=W, extending 3.4.6(2), p. 322. *)
  complex_weierstrass_preparation_identity:Q*Phi=W;
  (** Source for [complex_weierstrass_preparation_unit_value]: the original
      multiplier is nonzero at zero, extending 3.4.6(2), p. 322. *)
  complex_weierstrass_preparation_unit_value:exists q:@holomorphic_representative_type R X NX hNX 0,
    holomorphic_germ q=Q /\holomorphic_representative_value q 0<>0;
  (** Source for [complex_weierstrass_preparation_polynomial]: the original
      monic polynomial and vanishing transverse coefficients, extending
      3.4.6(2), p. 322, under 3.4.12, p. 339. *)
  complex_weierstrass_preparation_polynomial:
    @is_complex_weierstrass_polynomial_germ xi projection k W Wi
}.
End Preparation.
