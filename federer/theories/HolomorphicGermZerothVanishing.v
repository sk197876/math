(** Federer (1969), 3.4.12, p. 339, extending 3.4.7,
    p. 325: zero value is exactly zero zeroth jet in
    the original holomorphic germ ring. Reuse the actual
    order-zero differential and opaque derivative laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP
  HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermJetsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [holomorphic_germ_zeroth_vanishing]: the original
    equation Phi(0)=0 in the complex finite-order argument,
    extending 3.4.7, p. 325. *)
Lemma holomorphic_germ_zeroth_vanishing (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:restricted_space (ComplexScalars.embed R) X->R) (hNX:is_real_norm NX) a
    (f:@holomorphic_representative_type R X NX hNX a):
  holomorphic_representative_value f a=0 <->
  @HolomorphicGermJets.value R X NX hNX a 0%N (holomorphic_germ f)=0.
Proof.
pose XR:=restricted_space (ComplexScalars.embed R) X.
pose CR:=restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o.
pose N:=@complex_modulus R.
pose hN:=@complex_modulus_real_norm R.
pose ev:=@ContinuousMultilinear.evaluation R 0%N XR CR NX N hNX hN.
pose jet:=@HolomorphicGermJets.value R X NX hNX a 0%N (holomorphic_germ f).
have hActual:=@HolomorphicGermJets.laws R X NX hNX a 0%N (holomorphic_germ f) f (erefl _).
split.
- move=>hValue;apply:(continuous_multilinear_extensional (@ContinuousMultilinear.laws R 0%N
    XR CR NX N hNX hN))=>u.
  have hu:u=[ffun _:'I_0=>(0:X)].
    by apply/ffunP=>i;have:=ltn_ord i;rewrite ltn0.
  rewrite hu linear0;exact:etrans hActual.2 hValue.
- move=>hJet;have hh:=hActual.2.
  by rewrite hJet linear0 in hh;exact:esym hh.
Qed.
