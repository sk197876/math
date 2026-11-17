(** Federer (1969), 3.4.12, p. 339: the real restriction
    of an original complex germ form has exactly its actual
    derivative norm. Apply the existing tuple/family norm theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus ComplexScalarNorm SymmetricForms SymmetricOperatorNorm
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearSymmetricNorm
  HolomorphicGermUP HolomorphicGermJetsSealed HolomorphicGermFormsUP HolomorphicGermFormsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [holomorphic_germ_real_form_norm]: the exact norm
    of the original (not reconstructed) derivative in the complex
    extension of the estimates of 3.4.6, pp. 322–323. *)
Theorem holomorphic_germ_real_form_norm (R:realType)
    (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX) a m
    (alpha:holomorphic_germ_space (complex_norm_real hNX) a)
    (G:S_m (restricted_space (ComplexScalars.embed R) X)
      (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) m):
  (forall t,G t=@HolomorphicGermForms.value R X NX hNX a m alpha t) ->
  @symmetric_operator_norm R (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (complex_norm_real hNX).1 (@complex_modulus R) m G=
    (@ContinuousMultilinear.norm R m (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R)
      (complex_norm_real hNX) (@complex_modulus_real_norm R)
      (@HolomorphicGermJets.value R X NX (complex_norm_real hNX) a m alpha))%:E.
Proof.
move=>hG.
apply:(@continuous_multilinear_symmetric_norm R m
  (restricted_space (ComplexScalars.embed R) X)
  (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) _ NX (@complex_modulus R)
  (complex_norm_real hNX) (@complex_modulus_real_norm R) _ _
  (@ContinuousMultilinear.laws R m (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R)
    (complex_norm_real hNX) (@complex_modulus_real_norm R)) _ G)=>t.
by rewrite hG (@HolomorphicGermForms.laws R X NX hNX a m alpha t).
Qed.
