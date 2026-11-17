(** Federer (1969), 3.4.12, pp. 338–339:
    original complex symmetric-form coefficients have the
    actual holomorphic germ-jet values. This independent equation
    precedes existence, uniqueness and opaque choice. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus
  ComplexScalarNorm SymmetricForms ContinuousMultilinearUP ContinuousMultilinearSealed
  HolomorphicGermUP HolomorphicGermJetsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_holomorphic_germ_form]: the original
    complex symmetric differential coefficient at the centre,
    3.4.12, pp. 338–339, specified by
    exact evaluation on every original tuple. *)
Definition is_holomorphic_germ_form (R:realType)
    (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX)
    (a:X) k (alpha:holomorphic_germ_space (complex_norm_real hNX) a)
    (F:S_m X (ComplexScalars.C R)^o k):Prop:=
  forall t,F t=@ContinuousMultilinear.evaluation R k
    (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
    NX (@complex_modulus R) (complex_norm_real hNX) (@complex_modulus_real_norm R)
    [ffun i=>tnth t i] (@HolomorphicGermJets.value R X NX (complex_norm_real hNX) a k alpha).
