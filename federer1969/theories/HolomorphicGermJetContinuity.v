(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 319: each
    actual derivative coordinate is continuous for the original germ metric. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermOperationsUP RealNormUP NormMetric ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm HolomorphicGermUP HolomorphicGermJetsSealed HolomorphicGermMetric
  JetSequenceMetricUP JetMetricCoordinateControl.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_germ_jet_continuous]: supporting
    closedness of the factorial-growth classes in 3.4.5,
    p. 319. The exact metric controls the norm of
    every coordinate difference with an explicit positive cutoff. *)
Theorem holomorphic_germ_jet_continuous (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X) m:
  continuous (fun alpha:@holomorphic_germ_metric R X NX hNX a=>
    (@HolomorphicGermJets.value R X NX hNX a m alpha:
      real_norm_metric_space (continuous_multilinear_norm_is_norm (@complex_modulus_real_norm R)
        (@ContinuousMultilinear.laws R m (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R))))).
Proof.
pose NS:=@complex_modulus R.
pose hNS:=@complex_modulus_real_norm R.
pose Z i:=@ContinuousMultilinear.space R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX NS hNX hNS.
pose N i:=@ContinuousMultilinear.norm R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX NS hNX hNS.
pose jet:=@HolomorphicGermJets.value R X NX hNX a.
pose d:=@holomorphic_germ_distance R X NX hNX a.
have hd:=@holomorphic_germ_distance_formula R X NX hNX a.
pose M:=@holomorphic_germ_metric R X NX hNX a.
pose Y:=real_norm_metric_space (continuous_multilinear_norm_is_norm hNS
  (@ContinuousMultilinear.laws R m (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX NS hNX hNS)).
move=>alpha U hU.
have [epsilon hEpsilon hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP (jet m alpha:Y) U) hU.
have [delta [hDelta hControl]]:=@jet_metric_coordinate_control R (holomorphic_germ_space hNX a) Z N jet d hd m epsilon hEpsilon.
apply:(proj2 (metricType_numDomainType.nbhs_mdistP (alpha:M) _)).
exists delta;first exact:hDelta.
move=>beta hSmall;apply:hBall.
change (is_true (N m (jet m alpha-jet m beta)<epsilon)).
apply:hControl.
by rewrite /d -holomorphic_germ_metric_distanceE.
Qed.
