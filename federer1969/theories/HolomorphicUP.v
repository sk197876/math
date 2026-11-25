(** Federer (1969), 3.4.12, p. 338:
    holomorphic means real analytic with complex linear
    first differential at each original domain point.
    The following definition includes no complex higher-jet,
    ring, preparation or stratification assertion. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed
  NormDifferentialUP NormAnalyticUP ComplexRealLinearMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_holomorphic]: the original additional
    condition on 3.1.24 in 3.4.12, p. 338.
    The source and target keep their complex scalar
    structures and their underlying real norms. Completeness
    is retained separately when a theorem uses it. *)
Definition is_holomorphic (R:realType) (X Y:lmodType (ComplexScalars.C R))
    (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm (fun x:restricted_space (ComplexScalars.embed R) X=>NX x))
    (hNY:is_real_norm (fun y:restricted_space (ComplexScalars.embed R) Y=>NY y))
    (A:set X) (f:X->Y):Prop:=
  @norm_analytic R (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) Y) NX NY hNX hNY A f /\
  forall x (L:Hom (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) Y)),
    A x ->@has_norm_differential R
      (restricted_space (ComplexScalars.embed R) X)
      (restricted_space (ComplexScalars.embed R) Y) NX NY A f x L ->is_complex_linear_real_map L.
