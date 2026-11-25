(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 319: the
    original derivative metric gives exactly coordinate convergence.
    This direction supports compactness and continuity of the
    algebra operations without assuming either conclusion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermOperationsUP RealNormUP NormMetric ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm HolomorphicGermUP HolomorphicGermJetsSealed HolomorphicGermMetric
  JetSequenceMetricUP JetMetricFiniteControl.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_germ_continuous_from_jets]: a map
    into the germ metric of 3.4.5, p. 319,
    is continuous when each actual derivative coordinate is
    continuous. Finite-prefix estimates control the full exact
    metric, including its infinite tail. *)
Theorem holomorphic_germ_continuous_from_jets (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X) (P:topologicalType)
    (f:P->@holomorphic_germ_metric R X NX hNX a):
  (forall m,continuous (fun p:P=>
    (@HolomorphicGermJets.value R X NX hNX a m (f p):
      real_norm_metric_space (continuous_multilinear_norm_is_norm (@complex_modulus_real_norm R)
        (@ContinuousMultilinear.laws R m (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R)))))) ->
  continuous f.
Proof.
move=>hCoordinates.
pose NS:=@complex_modulus R.
pose hNS:=@complex_modulus_real_norm R.
pose Z i:=@ContinuousMultilinear.space R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX NS hNX hNS.
pose N i:=@ContinuousMultilinear.norm R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX NS hNX hNS.
pose hN i:=continuous_multilinear_norm_is_norm hNS
  (@ContinuousMultilinear.laws R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX NS hNX hNS).
pose jet:=@HolomorphicGermJets.value R X NX hNX a.
pose d:=@holomorphic_germ_distance R X NX hNX a.
have hd:=@holomorphic_germ_distance_formula R X NX hNX a.
move=>p U hU.
have [epsilon hEpsilon hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP (f p) U) hU.
have [K [delta [hDelta hControl]]]:=@jet_metric_finite_coordinate_control R
  (holomorphic_germ_space hNX a) Z N hN jet d hd epsilon hEpsilon.
have hNear (i:'I_K):nbhs p [set q:P|N i (jet i (f p)-jet i (f q))<delta].
  have hBallN:nbhs (jet i (f p):real_norm_metric_space (hN i))
      [set z:real_norm_metric_space (hN i)|N i (jet i (f p)-z)<delta].
    apply:(proj2 (metricType_numDomainType.nbhs_mdistP (jet i (f p):real_norm_metric_space (hN i)) _)).
    exists delta;first exact:hDelta.
    by move=>z hz.
  exact:(hCoordinates i p _ hBallN).
have hAll:=@filter_forall P (Finite.clone 'I_K _) _ (nbhs p) (nbhs_filter p) hNear.
apply:filterS hAll=>q hq;apply:hBall.
change (is_true (d (f p) (f q)<epsilon)).
apply:hControl=>m hm;exact:(hq (Ordinal hm)).
Qed.
