(** Federer (1969), 3.4.12, p. 339:
    original holomorphic subvarieties are specified by
    finite original complex equations on an open domain.
    This definition includes repeated and empty equation families
    and assumes no decomposition or dimension theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm
  NormMetric HolomorphicUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_finite_holomorphic_variety]: the original
    replacement of finite analytic equations in 3.4.5,
    p. 320, by holomorphic equations as specified
    in 3.4.12, p. 339. *)
Definition is_finite_holomorphic_variety (R:realType)
    (X:lmodType (ComplexScalars.C R))
    (NX:restricted_space (ComplexScalars.embed R) X->R)
    (hNX:is_real_norm NX) (U S:set X):Prop:=
  @open (real_norm_metric_space hNX) U /\
  exists I:finType,exists f:I->X->ComplexScalars.C R,
    (forall i,@is_holomorphic R X (ComplexScalars.C R)^o NX (@complex_modulus R)
      hNX (@complex_modulus_real_norm R) U (f i)) /\
    forall x,S x <->U x /\forall i,f i x=0.
