(** Federer (1969), 3.4.12, p. 339, extending 3.4.7, p. 325: the
    original coordinate powers have their actual ring-power
    germs. These supporting representative equations justify
    the finite transverse remainder module. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed HolomorphicGermArithmeticRepresentatives RealNormUP HolomorphicGermRepresentatives HolomorphicGermOperationsUP HolomorphicGermUP
  HolomorphicGermSealed HolomorphicGermRingLaws HolomorphicGermRing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [holomorphic_representative_power_exists]:
    the powers 1, xi, ..., xi^(k-1) used
    in 3.4.7, p. 325, have actual analytic
    representatives and their germs are the corresponding
    powers in the original opaque ring. *)
Theorem holomorphic_representative_power_exists (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a
    (f:@holomorphic_representative_type R X NX hNX a) i:
  exists g:@holomorphic_representative_type R X NX hNX a,
    (forall x,holomorphic_representative_value g x = (holomorphic_representative_value f x)^+i) /\
    (holomorphic_germ g:@holomorphic_germ_ring R X NX hNX a) =
      (holomorphic_germ f:@holomorphic_germ_ring R X NX hNX a)^+i.
Proof.
elim:i=>[|i [g [hValues hGerm]]].
- exists (@holomorphic_constant_representative R X NX hNX a 1);split.
  + move=>x;by rewrite expr0.
  + by rewrite expr0.
- exists (@holomorphic_multiply_representatives R X NX hNX a f g);split.
  + move=>x;change (holomorphic_representative_value f x*holomorphic_representative_value g x =
      (holomorphic_representative_value f x)^+i.+1).
    by rewrite hValues exprS.
  + rewrite -(@holomorphic_germ_multiply_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNX a)).
    change ((holomorphic_germ f:@holomorphic_germ_ring R X NX hNX a)*holomorphic_germ g =
      (holomorphic_germ f:@holomorphic_germ_ring R X NX hNX a)^+i.+1).
    by rewrite hGerm exprS.
Qed.
