(** Federer (1969), 3.4.12, p. 339:
    holomorphic ring operations are independently specified
    by their original representative equations before existence
    and opaque sealing. No division or factorization assertion
    is included among these defining equations. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed
  HolomorphicGermRepresentatives HolomorphicGermArithmeticRepresentatives HolomorphicGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_holomorphic_germ_operations]: the original
    holomorphic ring operations in the replacement of
    3.4.5 specified by 3.4.12, p. 339. *)
Record is_holomorphic_germ_operations (R:realType)
    (X:lmodType (ComplexScalars.C R))
    (NX:restricted_space (ComplexScalars.embed R) X->R)
    (hNX:is_real_norm NX) (a:X)
    (add mul:holomorphic_germ_space hNX a->holomorphic_germ_space hNX a->holomorphic_germ_space hNX a)
    (opp:holomorphic_germ_space hNX a->holomorphic_germ_space hNX a):Prop:={
  (** Source for [holomorphic_germ_add_equation]: the original
      pointwise addition equation, 3.4.12, p. 339. *)
  holomorphic_germ_add_equation:forall f g,
    add (holomorphic_germ f) (holomorphic_germ g)=
      holomorphic_germ (@holomorphic_add_representatives R X NX hNX a f g);
  (** Source for [holomorphic_germ_multiply_equation]: the original
      pointwise multiplication equation, 3.4.12, p. 339. *)
  holomorphic_germ_multiply_equation:forall f g,
    mul (holomorphic_germ f) (holomorphic_germ g)=
      holomorphic_germ (@holomorphic_multiply_representatives R X NX hNX a f g);
  (** Source for [holomorphic_germ_negate_equation]: the original
      pointwise additive-inverse equation, 3.4.12, p. 339. *)
  holomorphic_germ_negate_equation:forall f,
    opp (holomorphic_germ f)=holomorphic_germ (@holomorphic_negate_representative R X NX hNX a f)
}.


(** Source for [holomorphic_germ_zero]: the original zero
    germ of the complex ring, 3.4.12, p. 339. *)
Definition holomorphic_germ_zero (R:realType)
    (X:lmodType (ComplexScalars.C R))
    (NX:restricted_space (ComplexScalars.embed R) X->R)
    (hNX:is_real_norm NX) (a:X):holomorphic_germ_space hNX a:=
  holomorphic_germ (@holomorphic_constant_representative R X NX hNX a 0).

(** Source for [holomorphic_germ_one]: the original unit
    germ of the complex ring, 3.4.12, p. 339. *)
Definition holomorphic_germ_one (R:realType)
    (X:lmodType (ComplexScalars.C R))
    (NX:restricted_space (ComplexScalars.embed R) X->R)
    (hNX:is_real_norm NX) (a:X):holomorphic_germ_space hNX a:=
  holomorphic_germ (@holomorphic_constant_representative R X NX hNX a 1).
