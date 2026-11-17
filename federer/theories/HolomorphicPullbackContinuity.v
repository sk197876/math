(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 319: analytic local
    maps induce continuous homomorphisms for the exact original
    germ metrics. Actual composition derivative bounds discharge
    continuity without any extra regularity or dimension hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicAtUP HolomorphicAtAnalytic HolomorphicGermAnalytic RealNormUP NormMetric NormAnalyticUP
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermMetric HolomorphicGermJetsSealed
  HolomorphicGermGrowthUP HolomorphicGermJetDifference HolomorphicGermMetricTopology
  HolomorphicGermFiniteCoordinateNeighbourhood
  HolomorphicPullbackUP HolomorphicPullbackSealed HolomorphicPullbackRing HolomorphicPullbackJetBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_germ_pullback_continuous]: the
    original continuous ring homomorphism of 3.4.5, p. 319.
    The finite-coordinate tolerance and the infinite metric tail
    are both proved, rather than supplied as hypotheses. *)
Theorem holomorphic_germ_pullback_continuous (R:realType) (X Y:lmodType (ComplexScalars.C R))
    (NX:X->R) (NY:Y->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY)
    (A:set X) (u:X->Y) a
    (hu:@is_holomorphic_at R X Y NX NY hNX hNY A u a):
  continuous (fun alpha:@holomorphic_germ_metric R Y NY hNY (u a)=>
    (@HolomorphicPullback.map R X Y NX NY hNX hNY A u a hu alpha:@holomorphic_germ_metric R X NX hNX a)).
Proof.
pose P:=@HolomorphicPullback.map R X Y NX NY hNX hNY A u a hu.
pose M:=@holomorphic_germ_metric R Y NY hNY (u a).
pose GY:=[the comNzRingType of (@holomorphic_germ_ring R Y NY hNY (u a))].
pose GX:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)].
pose jet:=@HolomorphicGermJets.value R X NX hNX a.
apply:(@holomorphic_germ_continuous_from_jets R X NX hNX a [the topologicalType of M] _)=>m.
pose N:=@ContinuousMultilinear.norm R m (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R).
pose hN:=continuous_multilinear_norm_is_norm (@complex_modulus_real_norm R)
  (@ContinuousMultilinear.laws R m (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R)).
pose T:=real_norm_metric_space hN.
have [K [hK hBound]]:=@holomorphic_germ_pullback_jet_bound R X Y NX NY hNX hNY A u a hu m.
move=>alpha0 U hU.
have [epsilon hEpsilon hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP (jet m (P alpha0):T) U) hU.
pose delta:R:=epsilon/(K+1).
have hDen:0<K+1 by rewrite addrC ltr_pwDl.
have hDelta:0<delta by rewrite /delta divr_gt0.
have hControl:K*delta<epsilon.
  have hFactor:delta*(K+1)=epsilon by rewrite /delta divfK ?gt_eqF.
  by rewrite -hFactor [K*delta]mulrC ltr_pM2l // ltrDl ltr01.
have hNear:=@holomorphic_germ_finite_coordinate_neighbourhood R Y NY hNY (u a) m alpha0 delta hDelta.
change (nbhs alpha0 (fun alpha:M=>forall i,(i<=m)%N ->
  @holomorphic_germ_jet_norm R Y NY hNY (u a) i ((alpha:GY)-(alpha0:GY))<delta)) in hNear.
change (nbhs alpha0 (fun alpha:M=>U (jet m (P alpha)))).
apply:filterS hNear=>alpha hAlpha;apply:hBall.
change (is_true (N (jet m (P alpha0)-jet m (P alpha))<epsilon)).
rewrite /N (real_seminorm_subtract hN.1).
have hEstimate:=hBound ((alpha:GY)-(alpha0:GY)) delta (ltW hDelta)
  (fun i hi=>ltW (hAlpha i hi)).
rewrite /P holomorphic_germ_pullback_difference /holomorphic_germ_jet_norm
  holomorphic_germ_jet_difference in hEstimate.
exact:le_lt_trans hEstimate hControl.
Qed.
