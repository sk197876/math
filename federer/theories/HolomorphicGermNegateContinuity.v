(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 319: negation
    is continuous for the original derivative metric. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermOperationsUP RealNormUP NormMetric NormMetricScaleContinuity
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  HolomorphicGermUP HolomorphicGermSealed HolomorphicGermJetsSealed HolomorphicGermJetZeroNegate
  HolomorphicGermMetric HolomorphicGermJetContinuity HolomorphicGermMetricTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [holomorphic_germ_negate_continuous]: continuity
    of the additive inverse in 3.4.5, p. 319,
    follows from actual derivative negation and the norm
    topology of each coordinate. *)
Theorem holomorphic_germ_negate_continuous (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X):
  continuous (fun alpha:@holomorphic_germ_metric R X NX hNX a=>
    (@HolomorphicGerms.opp R X NX hNX a alpha:@holomorphic_germ_metric R X NX hNX a)).
Proof.
pose M:=@holomorphic_germ_metric R X NX hNX a.
apply:(@holomorphic_germ_continuous_from_jets R X NX hNX a [the topologicalType of M] _)=>m.
pose Z:=@ContinuousMultilinear.space R m (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R).
pose N:=@ContinuousMultilinear.norm R m (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R).
pose hN:=continuous_multilinear_norm_is_norm (@complex_modulus_real_norm R)
  (@ContinuousMultilinear.laws R m (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R)).
pose Y:=real_norm_metric_space hN.
pose jet:=fun alpha:M=>(@HolomorphicGermJets.value R X NX hNX a m alpha:Y).
have hJet:continuous jet:=@holomorphic_germ_jet_continuous R X NX hNX a m.
have hEquation:(fun alpha:M=>@HolomorphicGermJets.value R X NX hNX a m
    (@HolomorphicGerms.opp R X NX hNX a alpha))=(fun alpha:M=>(-1:R)*:jet alpha).
  apply:funext=>alpha;rewrite scaleN1r;exact:holomorphic_germ_jet_negate.
rewrite hEquation=>alpha W hW.
exact:(hJet alpha _ (@real_norm_metric_scale_continuous R Z N hN (-1) (jet alpha) W hW)).
Qed.
