(** Federer (1969), 3.4.5, p. 319: actual
    functional multiplication is continuous for the original
    derivative-series germ metric. The finite Leibniz estimate
    supplies every required coordinate tolerance. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric AnalyticGermUP AnalyticGermSealed AnalyticGermRing AnalyticGermMetric
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  AnalyticGermJetsSealed AnalyticGermGrowthUP AnalyticGermJetDifference AnalyticGermMetricTopology
  AnalyticGermProductCoordinateControl AnalyticGermFiniteCoordinateNeighbourhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_germ_multiply_continuous]: the
    multiplication continuity asserted in 3.4.5, p. 319,
    for the exact original metric, without finite-dimensional
    or extra continuity hypotheses. *)
Theorem analytic_germ_multiply_continuous (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X):
  continuous (fun p:(@analytic_germ_metric R X NX hNX a)*(@analytic_germ_metric R X NX hNX a)=>
    (@AnalyticGerms.mul R X NX hNX a p.1 p.2:@analytic_germ_metric R X NX hNX a)).
Proof.
pose M:=@analytic_germ_metric R X NX hNX a.
pose A:=[the comNzRingType of (@analytic_germ_ring R X NX hNX a)].
pose mul:=@AnalyticGerms.mul R X NX hNX a.
pose jet:=@AnalyticGermJets.value R X NX hNX a.
apply:(@analytic_germ_continuous_from_jets R X NX hNX a [the topologicalType of (M*M)%type] _)=>m.
pose N:=@ContinuousMultilinear.norm R m X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R).
pose hN:=continuous_multilinear_norm_is_norm (@scalar_absolute_value_norm R)
  (@ContinuousMultilinear.laws R m X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R)).
pose Y:=real_norm_metric_space hN.
move=>p U hU.
have [epsilon hEpsilon hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP (jet m (mul p.1 p.2):Y) U) hU.
have [delta [hDelta hControl]]:=@analytic_germ_product_finite_coordinate_control R X NX hNX a m p.1 p.2 epsilon hEpsilon.
pose V (alpha0:M):set M:=fun alpha=>forall i,(i<=m)%N ->
  @analytic_germ_jet_norm R X NX hNX a i ((alpha:A)-(alpha0:A))<delta.
have hV alpha0:nbhs alpha0 (V alpha0).
  exact:(@analytic_germ_finite_coordinate_neighbourhood R X NX hNX a m alpha0 delta hDelta).
exists (V p.1,V p.2);first by split;exact:hV.
move=>[alpha beta] [hAlpha hBeta];apply:hBall.
change (is_true (N (jet m (mul p.1 p.2)-jet m (mul alpha beta))<epsilon)).
rewrite /N (real_seminorm_subtract hN.1).
have hSmall:=hControl (alpha:A) (beta:A)
  (fun i hi=>ltW (hAlpha i hi)) (fun i hi=>ltW (hBeta i hi)).
rewrite /analytic_germ_jet_norm analytic_germ_jet_difference in hSmall.
exact:hSmall.
Qed.
