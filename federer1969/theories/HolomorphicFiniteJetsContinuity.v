(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(5), p. 328:
    the actual finite derivative prefix is continuous
    for the original germ metric. The proof uses
    each actual derivative's continuity from 3.4.5,
    p. 319, and the abstract finite-product topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm Hom RealNormUP NormMetric NormedFamilyUP NormedFamilySealed
  NormedFamilyContinuousAssembly ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm HolomorphicGermRing HolomorphicGermMetric HolomorphicGermJetsSealed HolomorphicGermJetContinuity
  HolomorphicFiniteJetsUP HolomorphicFiniteJetsSealed HolomorphicFiniteJetsLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [holomorphic_finite_jet_map_continuous]: the
    finite-prefix map for the actual metric of
    3.4.5, p. 319, is continuous, supporting the
    expanded ideal-closedness proof for 3.4.8(5), p. 328. *)
Theorem holomorphic_finite_jet_map_continuous (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:X->R) (hNX:is_complex_norm NX) m a:
  continuous (fun alpha:@holomorphic_germ_metric R X NX (complex_norm_real hNX) a=>
    (@HolomorphicFiniteJets.map R X NX hNX m a alpha:
      real_norm_metric_space (@holomorphic_finite_jet_norm_laws R X NX hNX m))).
Proof.
pose Z:=fun i:'I_m=>@ContinuousMultilinear.space R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_norm_real hNX) (@complex_modulus_real_norm R).
pose N:=fun i:'I_m=>@ContinuousMultilinear.norm R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_norm_real hNX) (@complex_modulus_real_norm R).
pose hN:=fun i:'I_m=>continuous_multilinear_norm_is_norm (@complex_modulus_real_norm R)
  (@ContinuousMultilinear.laws R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_norm_real hNX) (@complex_modulus_real_norm R)).
apply:(@normed_family_continuous_assembly R m Z N hN
  (@holomorphic_finite_jet_space R X NX hNX m)
  (@holomorphic_finite_jet_coordinate R X NX hNX m)
  (@holomorphic_finite_jet_norm R X NX hNX m)
  (@NormedFamily.laws R m Z N)
  [the topologicalType of (@holomorphic_germ_metric R X NX (complex_norm_real hNX) a)]
  (@HolomorphicFiniteJets.map R X NX hNX m a))=>i.
have hEquation:(fun alpha:@holomorphic_germ_metric R X NX (complex_norm_real hNX) a=>
    @holomorphic_finite_jet_coordinate R X NX hNX m i (@HolomorphicFiniteJets.map R X NX hNX m a alpha)) =
    (fun alpha:@holomorphic_germ_metric R X NX (complex_norm_real hNX) a=>@HolomorphicGermJets.value R X NX (complex_norm_real hNX) a i alpha).
  apply:funext=>alpha;exact:(@HolomorphicFiniteJets.laws R X NX hNX m a alpha i).
rewrite hEquation;exact:(@holomorphic_germ_jet_continuous R X NX (complex_norm_real hNX) a i).
Qed.
