(** Federer (1969), 3.4.12, pp. 338–339:
    original holomorphic functions have open actual domains,
    as in 3.1.24, p. 239. Reuse their
    proved real analytic continuity on the same domain. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed
  NormDifferentialUP NormRegularity NormAnalyticLocal HolomorphicUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [holomorphic_domain_interior]: every point
    of the original holomorphic domain is an interior
    point for its original norm, 3.4.12,
    pp. 338–339. No domain extension is chosen. *)
Theorem holomorphic_domain_interior (R:realType)
    (X Y:lmodType (ComplexScalars.C R))
    (NX:restricted_space (ComplexScalars.embed R) X->R)
    (NY:restricted_space (ComplexScalars.embed R) Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (f:X->Y):
  is_holomorphic hNX hNY A f ->forall a,A a ->norm_domain_interior NX A a.
Proof.
move=>hF a ha;have hClass:=norm_analytic_class_all_orders hF.1 0%N.
exact:(hClass.1 a ha).1.
Qed.
