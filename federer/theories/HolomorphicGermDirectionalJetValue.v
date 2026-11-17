(** Federer (1969), 3.4.12, p. 339: the original
    divided complex coefficient is the actual real jet evaluation
    divided by the same complex factorial. This is the exact
    scalar restriction connection in the Taylor argument. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm
  ContinuousMultilinearSealed HolomorphicGermUP HolomorphicGermRing HolomorphicGermJetsSealed
  HolomorphicGermDirectionalCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [holomorphic_germ_directional_coefficient_jet_value]:
    the original D^k(alpha)[v^k]/k! value, extending
    3.4.5, p. 319, under 3.4.12, p. 339. *)
Lemma holomorphic_germ_directional_coefficient_jet_value (R:realType)
    (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX) a k
    (alpha:@holomorphic_germ_ring R X NX (complex_norm_real hNX) a) v:
  @holomorphic_germ_directional_coefficient R X NX hNX a k alpha v=
    ((k`!)%:R:ComplexScalars.C R)^-1*@ContinuousMultilinear.evaluation R k
      (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
      NX (@complex_modulus R) (complex_norm_real hNX) (@complex_modulus_real_norm R)
      [ffun _:'I_k=>v] (@HolomorphicGermJets.value R X NX (complex_norm_real hNX) a k alpha).
Proof.
rewrite holomorphic_germ_directional_coefficient_real_value.
change (ComplexScalars.embed R (((k`!)%:R:R)^-1)*
  (@ContinuousMultilinear.evaluation R k (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R)
    (complex_norm_real hNX) (@complex_modulus_real_norm R) [ffun _:'I_k=>v]
    (@HolomorphicGermJets.value R X NX (complex_norm_real hNX) a k alpha))=
  ((k`!)%:R:ComplexScalars.C R)^-1*
  (@ContinuousMultilinear.evaluation R k (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R)
    (complex_norm_real hNX) (@complex_modulus_real_norm R) [ffun _:'I_k=>v]
    (@HolomorphicGermJets.value R X NX (complex_norm_real hNX) a k alpha))).
by rewrite fmorphV rmorph_nat.
Qed.
