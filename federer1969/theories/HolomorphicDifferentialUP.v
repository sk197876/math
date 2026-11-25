(** Federer (1969), 3.4.12, p. 338:
    independent laws for the original complex linear
    differential. Its actual real differential graph and
    every underlying value are retained; existence and
    uniqueness are proved separately from this specification. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed NormDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_holomorphic_differential]: Df(x) in
    3.4.12, p. 338, as an actual
    complex linear map representing the already defined
    real differential. No choice of derivative is exposed. *)
Definition is_holomorphic_differential (R:realType)
    (X Y:lmodType (ComplexScalars.C R)) (NX:X->R) (NY:Y->R)
    (A:set X) (f:X->Y) a (D:Hom X Y):Prop:=
  exists L:Hom (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) Y),
    @has_norm_differential R
      (restricted_space (ComplexScalars.embed R) X)
      (restricted_space (ComplexScalars.embed R) Y) NX NY A f a L /\forall x,D x=L x.
