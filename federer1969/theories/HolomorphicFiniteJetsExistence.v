(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(5), p. 328:
    the existing finite-product universal property supplies
    actual finite-jet maps. Product extensionality proves
    uniqueness; every germ derivative remains unchanged. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm Hom RealNormUP NormedFamilyUP NormedFamilySealed
  ContinuousMultilinearUP ContinuousMultilinearSealed HolomorphicGermRing
  HolomorphicGermJetsSealed HolomorphicFiniteJetsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [holomorphic_finite_jet_map_exists]: the
    finite derivative prefix from 3.4.5, p. 319,
    exists in the existing abstract product, supporting
    the ideal-closedness proof for 3.4.8(5), p. 328. *)
Theorem holomorphic_finite_jet_map_exists (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:X->R) (hNX:is_complex_norm NX) m a:
  exists f:@holomorphic_germ_ring R X NX (complex_norm_real hNX) a->@holomorphic_finite_jet_space R X NX hNX m,
    is_holomorphic_finite_jet_map f.
Proof.
pose Z:=fun i:'I_m=>@ContinuousMultilinear.space R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_norm_real hNX) (@complex_modulus_real_norm R).
pose N:=fun i:'I_m=>@ContinuousMultilinear.norm R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_norm_real hNX) (@complex_modulus_real_norm R).
have hP:=@NormedFamily.laws R m Z N.
have hEach alpha:exists u:@holomorphic_finite_jet_space R X NX hNX m,
    forall i,@holomorphic_finite_jet_coordinate R X NX hNX m i u =
      @HolomorphicGermJets.value R X NX (complex_norm_real hNX) a i alpha.
  have [u hu]:=normed_family_surjective hP [ffun i:'I_m=>@HolomorphicGermJets.value R X NX (complex_norm_real hNX) a i alpha].
  exists u=>i;by rewrite hu ffunE.
have [f hF]:=choice hEach;exists f;exact:hF.
Qed.

(** Source for [holomorphic_finite_jet_map_unique]: actual
    derivative coordinates determine the finite prefix map
    uniquely, supporting 3.4.8(5), p. 328, from
    the original derivative metric in 3.4.5, p. 319. *)
Lemma holomorphic_finite_jet_map_unique (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:X->R) (hNX:is_complex_norm NX) m a
  (f g:@holomorphic_germ_ring R X NX (complex_norm_real hNX) a->@holomorphic_finite_jet_space R X NX hNX m):
  is_holomorphic_finite_jet_map f ->is_holomorphic_finite_jet_map g ->f = g.
Proof.
move=>hf hg;apply:funext=>alpha.
apply:(normed_family_extensional (@NormedFamily.laws R m
  (fun i:'I_m=>@ContinuousMultilinear.space R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_norm_real hNX) (@complex_modulus_real_norm R))
  (fun i:'I_m=>@ContinuousMultilinear.norm R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_norm_real hNX) (@complex_modulus_real_norm R))))=>i.
by rewrite hf hg.
Qed.
