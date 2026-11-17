(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(5), p. 328:
    finite prefixes retain actual derivative arithmetic,
    have a compatible norm, and are finite dimensional
    when the original source is finite dimensional.
    Every proof uses the existing opaque product laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm Hom RealNormUP LinearBasis NormedFamilyUP NormedFamilySealed
  NormedFamilyLaws NormedFamilyFiniteBasis ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm FiniteComplexMultilinearCoordinates HolomorphicGermUP HolomorphicGermRing HolomorphicGermSealed HolomorphicGermJetsSealed
  HolomorphicGermJetArithmetic HolomorphicGermJetZeroNegate HolomorphicGermRepresentatives
  HolomorphicGermArithmeticRepresentatives HolomorphicGermRealScalarJet ComplexWeierstrassScalarGermArithmetic HolomorphicFiniteJetsUP HolomorphicFiniteJetsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Laws.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:is_complex_norm NX.
Variable m:nat.
Local Notation Z:=(fun i:'I_m=>@ContinuousMultilinear.space R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_norm_real hNX) (@complex_modulus_real_norm R)).
Local Notation N:=(fun i:'I_m=>@ContinuousMultilinear.norm R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_norm_real hNX) (@complex_modulus_real_norm R)).
Local Notation P:=(@holomorphic_finite_jet_space R X NX hNX m).

(** Source for [holomorphic_finite_jet_norm_laws]: the
    finite sum of actual derivative norms is a norm,
    supporting 3.4.8(5), p. 328, with the product
    of 3.1.1(4), p. 210. *)
Lemma holomorphic_finite_jet_norm_laws:is_real_norm (@holomorphic_finite_jet_norm R X NX hNX m).
Proof.
apply:(@normed_family_is_norm R m Z N _ P
  (@holomorphic_finite_jet_coordinate R X NX hNX m) (@holomorphic_finite_jet_norm R X NX hNX m)
  (@NormedFamily.laws R m Z N))=>i.
exact:(continuous_multilinear_norm_is_norm (@complex_modulus_real_norm R)
  (@ContinuousMultilinear.laws R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_norm_real hNX) (@complex_modulus_real_norm R))).
Qed.

(** Source for [holomorphic_finite_jet_basis_exists]: finite
    source dimension gives finite-dimensional actual derivative
    prefixes, supporting 3.4.8(5), p. 328, from
    1.10.5, p. 47, and 1.6.1, p. 23. *)
Lemma holomorphic_finite_jet_basis_exists n (b:'I_n->(restricted_space (ComplexScalars.embed R) X)) (hb:is_basis b):
  exists q (e:'I_q->P),is_basis e.
Proof.
apply:(@normed_family_finite_basis_exists R m Z N P
  (@holomorphic_finite_jet_coordinate R X NX hNX m) (@holomorphic_finite_jet_norm R X NX hNX m)
  (@NormedFamily.laws R m Z N))=>i.
have [q [e [he _]]]:=@finite_complex_multilinear_basis_exists R (restricted_space (ComplexScalars.embed R) X) NX (complex_norm_real hNX) n b hb i.
by exists q,e.
Qed.

Variable a:X.
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX (complex_norm_real hNX) a)].
Local Notation f:=(@HolomorphicFiniteJets.map R X NX hNX m a).

(** Source for [holomorphic_finite_jet_zero]: the original
    zero germ has zero finite derivative prefix,
    supporting 3.4.8(5), p. 328, from 3.4.5, p. 319. *)
Lemma holomorphic_finite_jet_zero:f 0 = 0.
Proof.
apply:(normed_family_extensional (@NormedFamily.laws R m Z N))=>i.
rewrite (@HolomorphicFiniteJets.laws R X NX hNX m a 0 i) linear0.
exact:(@holomorphic_germ_jet_zero R X NX (complex_norm_real hNX) a i).
Qed.

(** Source for [holomorphic_finite_jet_add]: the actual
    finite derivative map preserves germ addition,
    supporting the same original derivative assertions. *)
Lemma holomorphic_finite_jet_add (alpha beta:G):f (alpha+beta) = f alpha+f beta.
Proof.
apply:(normed_family_extensional (@NormedFamily.laws R m Z N))=>i.
rewrite linearD /= !(@HolomorphicFiniteJets.laws R X NX hNX m a).
exact:(@holomorphic_germ_jet_add R X NX (complex_norm_real hNX) a i alpha beta).
Qed.

(** Source for [holomorphic_finite_jet_scale]: multiplying by
    an original scalar constant scales the entire actual
    finite prefix, supporting 3.4.8(5), p. 328,
    from the derivative arithmetic of 3.4.5, p. 319. *)
Lemma holomorphic_finite_jet_scale (c:R) (alpha:G):
  f ((holomorphic_germ (@holomorphic_constant_representative R X NX (complex_norm_real hNX) a (ComplexScalars.embed R c)):G)*alpha) = c*:f alpha.
Proof.
apply:(normed_family_extensional (@NormedFamily.laws R m Z N))=>i.
rewrite linearZ /= !(@HolomorphicFiniteJets.laws R X NX hNX m a).
exact:(@holomorphic_germ_real_scalar_jet R X NX hNX a i c alpha).
Qed.

(** Source for [holomorphic_finite_jet_equality]: equality
    of finite prefixes is exactly equality of every
    original derivative below the specified cutoff,
    supporting 3.4.8(5), p. 328, and the
    derivative coordinates of 3.4.5, p. 319. *)
Lemma holomorphic_finite_jet_equality (alpha beta:G):
  f alpha = f beta <->forall i,(i<m)%N ->
    @HolomorphicGermJets.value R X NX (complex_norm_real hNX) a i alpha = @HolomorphicGermJets.value R X NX (complex_norm_real hNX) a i beta.
Proof.
split.
- move=>hEqual i hi.
  have hValue:=congr1 (@holomorphic_finite_jet_coordinate R X NX hNX m (Ordinal hi)) hEqual.
  by rewrite !(@HolomorphicFiniteJets.laws R X NX hNX m a) in hValue.
- move=>hEqual;apply:(normed_family_extensional (@NormedFamily.laws R m Z N))=>i.
  rewrite !(@HolomorphicFiniteJets.laws R X NX hNX m a).
  exact:hEqual i (ltn_ord i).
Qed.
End Laws.
