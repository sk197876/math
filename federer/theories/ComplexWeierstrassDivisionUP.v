(** Federer (1969), 3.4.12, p. 339: independently specify
    the original complex division equation and its neighbourhood
    remainder condition before proving division and uniqueness. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP NormAnalyticUP
  HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRing HolomorphicUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Division.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o).
Variable NX:XR->R.
Variable hNX:is_real_norm NX.
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).
Local Notation Z:=(fun i=>@ContinuousMultilinear.space R i XR CR NX N hNX hN).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i XR CR NX N hNX hN).
Local Notation ZN:=(fun i=>@ContinuousMultilinear.norm R i XR CR NX N hNX hN).

(** Source for [is_complex_directional_polynomial_germ]: one original
    holomorphic representative has every actual derivative of order
    at least k zero along v throughout one neighbourhood,
    as in the complex extension of 3.4.6(1), p. 322. *)
Definition is_complex_directional_polynomial_germ (k:nat) (v:X)
    (rho:holomorphic_germ_space hNX (0:X)):Prop:=
  exists f:@holomorphic_representative_type R X NX hNX 0,
    holomorphic_germ f=rho /\exists U:set X,U 0 /\
    is_holomorphic hNX hN U (holomorphic_representative_value f) /\
    forall i,(k<=i)%N ->forall x,U x ->forall z:Z i,
      has_norm_higher_differential NX ev ZN setT (holomorphic_representative_value f) i x z ->
      @ev i [ffun _:'I_i=>v] z=0.

(** Source for [is_complex_weierstrass_division]: the original
    germ division equation and actual neighbourhood remainder law,
    3.4.12, p. 339, extending 3.4.6(1), p. 322. *)
Record is_complex_weierstrass_division (k:nat) (v:X)
    (phi psi quotient remainder:@holomorphic_germ_ring R X NX hNX 0):Prop:={
  (** Source for [complex_weierstrass_division_identity]: the actual
      original complex germ equation, 3.4.12, p. 339. *)
  complex_weierstrass_division_identity:psi=quotient*phi+remainder;
  (** Source for [complex_weierstrass_division_polynomial_remainder]: the
      original all-nearby-point derivative condition, extending 3.4.6(1),
      p. 322, under 3.4.12, p. 339. *)
  complex_weierstrass_division_polynomial_remainder:is_complex_directional_polynomial_germ k v remainder
}.
End Division.
