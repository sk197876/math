(** Federer (1969), 3.4.6(1), p. 322: the actual
    quotient and directional polynomial remainder, specified
    independently of a construction or existence theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP
  NormAnalyticUP AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_directional_polynomial_germ]: one actual
    analytic representative has every directional derivative of
    order at least k zero on a single neighbourhood of
    zero, as required in 3.4.6(1), p. 322. *)
Definition is_directional_polynomial_germ (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (k:nat) (v:X)
    (rho:analytic_germ_space hNX (0:X)):Prop:=
  exists f:@analytic_representative_type R X NX hNX 0,
    analytic_germ f=rho /\exists U:set X,U 0 /\
    @norm_analytic R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)
      U (analytic_representative_value f) /\
    forall i,(k<=i)%N ->forall x,U x ->
      forall z:@ContinuousMultilinear.space R i X R^o NX (fun t=>`|t|)
        hNX (@scalar_absolute_value_norm R),
      has_norm_higher_differential NX
        (fun j=>@ContinuousMultilinear.evaluation R j X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R))
        (fun j=>@ContinuousMultilinear.norm R j X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R))
        setT (analytic_representative_value f) i x z ->
      @ContinuousMultilinear.evaluation R i X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)
        [ffun _:'I_i=>v] z=0.

(** Source for [is_weierstrass_division]: the original
    germ identity psi=Q*phi+R and the actual directional
    polynomial condition for R, in 3.4.6(1), p. 322.
    Existence and uniqueness are separate proof obligations. *)
Record is_weierstrass_division (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (k:nat) (v:X)
    (phi psi quotient remainder:@analytic_germ_ring R X NX hNX 0):Prop:={
  (** Source for [weierstrass_division_identity]: the original
      analytic germ division equation, 3.4.6(1), p. 322. *)
  weierstrass_division_identity:psi=quotient*phi+remainder;
  (** Source for [weierstrass_division_polynomial_remainder]: the
      original remainder has every actual directional derivative
      of order at least k zero near zero, 3.4.6(1), p. 322. *)
  weierstrass_division_polynomial_remainder:@is_directional_polynomial_germ R X NX hNX k v remainder
}.
