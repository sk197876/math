(** Federer (1969), 3.4.12, p. 338: original holomorphy
    at a point includes real analyticity at that point. The
    same actual neighbourhood and original function are retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed NormAnalyticUP
  NormAnalyticDomain HolomorphicAtUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [holomorphic_at_analytic]: the original underlying
    real analytic condition of 3.1.24, p. 239, in
    the holomorphic definition of 3.4.12, p. 338. *)
Lemma holomorphic_at_analytic (R:realType) (X Y:lmodType (ComplexScalars.C R))
    (NX:X->R) (NY:Y->R)
    (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX)
    (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY)
    (A:X->Prop) (f:X->Y) a:
  @is_holomorphic_at R X Y NX NY hNX hNY A f a ->
  @norm_analytic_at R (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) Y) NX NY hNX hNY A f a.
Proof.
move=>[U [ha [hUA hF]]].
exact:(@norm_analytic_at_domain_enlargement R (restricted_space (ComplexScalars.embed R) X)
  (restricted_space (ComplexScalars.embed R) Y) NX NY hNX hNY U A f a hUA (hF.1 a ha)).
Qed.
