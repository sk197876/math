(** Federer (1969), 3.4.5, p. 319: each
    actual derivative coordinate is continuous for the original germ metric. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm AnalyticGermUP AnalyticGermJetsSealed AnalyticGermMetric
  JetSequenceMetricUP JetMetricCoordinateControl.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_germ_jet_continuous]: supporting
    closedness of the factorial-growth classes in 3.4.5,
    p. 319. The exact metric controls the norm of
    every coordinate difference with an explicit positive cutoff. *)
Theorem analytic_germ_jet_continuous (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) m:
  continuous (fun alpha:@analytic_germ_metric R X NX hNX a=>
    (@AnalyticGermJets.value R X NX hNX a m alpha:
      real_norm_metric_space (continuous_multilinear_norm_is_norm (@scalar_absolute_value_norm R)
        (@ContinuousMultilinear.laws R m X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R))))).
Proof.
pose NS:=fun t:R^o=>`|t|.
pose hNS:=@scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i X R^o NX NS hNX hNS.
pose N i:=@ContinuousMultilinear.norm R i X R^o NX NS hNX hNS.
pose jet:=@AnalyticGermJets.value R X NX hNX a.
pose d:=@analytic_germ_distance R X NX hNX a.
have hd:=@analytic_germ_distance_formula R X NX hNX a.
pose M:=@analytic_germ_metric R X NX hNX a.
pose Y:=real_norm_metric_space (continuous_multilinear_norm_is_norm hNS
  (@ContinuousMultilinear.laws R m X R^o NX NS hNX hNS)).
move=>alpha U hU.
have [epsilon hEpsilon hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP (jet m alpha:Y) U) hU.
have [delta [hDelta hControl]]:=@jet_metric_coordinate_control R (analytic_germ_space hNX a) Z N jet d hd m epsilon hEpsilon.
apply:(proj2 (metricType_numDomainType.nbhs_mdistP (alpha:M) _)).
exists delta;first exact:hDelta.
move=>beta hSmall;apply:hBall.
change (is_true (N m (jet m alpha-jet m beta)<epsilon)).
apply:hControl.
by rewrite /d -analytic_germ_metric_distanceE.
Qed.
