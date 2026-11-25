(** Federer (1969), 3.4.5, p. 319: the
    original derivative metric gives exactly coordinate convergence.
    This direction supports compactness and continuity of the
    algebra operations without assuming either conclusion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm AnalyticGermUP AnalyticGermJetsSealed AnalyticGermMetric
  JetSequenceMetricUP JetMetricFiniteControl.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_germ_continuous_from_jets]: a map
    into the germ metric of 3.4.5, p. 319,
    is continuous when each actual derivative coordinate is
    continuous. Finite-prefix estimates control the full exact
    metric, including its infinite tail. *)
Theorem analytic_germ_continuous_from_jets (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) (P:topologicalType)
    (f:P->@analytic_germ_metric R X NX hNX a):
  (forall m,continuous (fun p:P=>
    (@AnalyticGermJets.value R X NX hNX a m (f p):
      real_norm_metric_space (continuous_multilinear_norm_is_norm (@scalar_absolute_value_norm R)
        (@ContinuousMultilinear.laws R m X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R)))))) ->
  continuous f.
Proof.
move=>hCoordinates.
pose NS:=fun z:R^o=>`|z|.
pose hNS:=@scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i X R^o NX NS hNX hNS.
pose N i:=@ContinuousMultilinear.norm R i X R^o NX NS hNX hNS.
pose hN i:=continuous_multilinear_norm_is_norm hNS
  (@ContinuousMultilinear.laws R i X R^o NX NS hNX hNS).
pose jet:=@AnalyticGermJets.value R X NX hNX a.
pose d:=@analytic_germ_distance R X NX hNX a.
have hd:=@analytic_germ_distance_formula R X NX hNX a.
move=>p U hU.
have [epsilon hEpsilon hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP (f p) U) hU.
have [K [delta [hDelta hControl]]]:=@jet_metric_finite_coordinate_control R
  (analytic_germ_space hNX a) Z N hN jet d hd epsilon hEpsilon.
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
