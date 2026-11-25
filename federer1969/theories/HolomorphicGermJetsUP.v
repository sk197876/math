(** Federer (1969), 3.4.12, p. 339:
    the actual higher differentials at the original
    centre are specified independently of each holomorphic
    representative. The same real derivative graph is retained;
    complex multilinearity is proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm
  NormDifferentialUP ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP
  HolomorphicGermRepresentatives HolomorphicGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_holomorphic_germ_jet]: the actual
    original m-th germ differential in the complex
    replacement of 3.4.5, p. 319, specified
    by 3.4.12, p. 339. This law
    assumes no jet existence or Taylor injectivity. *)
Definition is_holomorphic_germ_jet (R:realType)
    (X:lmodType (ComplexScalars.C R))
    (NX:restricted_space (ComplexScalars.embed R) X->R)
    (hNX:is_real_norm NX) (a:X) m
    (alpha:holomorphic_germ_space hNX a)
    (z:@ContinuousMultilinear.space R m (restricted_space (ComplexScalars.embed R) X)
      (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
      NX (@complex_modulus R) hNX (@complex_modulus_real_norm R)):=
  forall f:@holomorphic_representative_type R X NX hNX a,
    holomorphic_germ f=alpha ->
    has_norm_higher_differential NX
      (fun i=>@ContinuousMultilinear.evaluation R i (restricted_space (ComplexScalars.embed R) X)
        (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
        NX (@complex_modulus R) hNX (@complex_modulus_real_norm R))
      (fun i=>@ContinuousMultilinear.norm R i (restricted_space (ComplexScalars.embed R) X)
        (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
        NX (@complex_modulus R) hNX (@complex_modulus_real_norm R))
      setT (holomorphic_representative_value f) m a z.
