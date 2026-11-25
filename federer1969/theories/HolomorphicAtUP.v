(** Federer (1969), 3.4.12, pp. 338–339: holomorphy at
    the original centre means holomorphy on an actual neighbourhood
    within the original domain, as in 3.1.24, p. 239. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed HolomorphicUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_holomorphic_at]: the local original function
    condition needed for the induced germ homomorphism of
    3.4.5, p. 319, over the complex field of 3.4.12, p. 339. *)
Definition is_holomorphic_at (R:realType) (X Y:lmodType (ComplexScalars.C R))
    (NX:X->R) (NY:Y->R)
    (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX)
    (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY)
    (A:X->Prop) (f:X->Y) a:Prop:=
  exists U:X->Prop,U a /\(forall x,U x ->A x) /\is_holomorphic hNX hNY U f.
