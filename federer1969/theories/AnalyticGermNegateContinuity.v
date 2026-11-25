(** Federer (1969), 3.4.5, p. 319: negation
    is continuous for the original derivative metric. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormMetricScaleContinuity
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  AnalyticGermUP AnalyticGermSealed AnalyticGermJetsSealed AnalyticGermJetZeroNegate
  AnalyticGermMetric AnalyticGermJetContinuity AnalyticGermMetricTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_germ_negate_continuous]: continuity
    of the additive inverse in 3.4.5, p. 319,
    follows from actual derivative negation and the norm
    topology of each coordinate. *)
Theorem analytic_germ_negate_continuous (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X):
  continuous (fun alpha:@analytic_germ_metric R X NX hNX a=>
    (@AnalyticGerms.opp R X NX hNX a alpha:@analytic_germ_metric R X NX hNX a)).
Proof.
pose M:=@analytic_germ_metric R X NX hNX a.
apply:(@analytic_germ_continuous_from_jets R X NX hNX a [the topologicalType of M] _)=>m.
pose Z:=@ContinuousMultilinear.space R m X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R).
pose N:=@ContinuousMultilinear.norm R m X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R).
pose hN:=continuous_multilinear_norm_is_norm (@scalar_absolute_value_norm R)
  (@ContinuousMultilinear.laws R m X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R)).
pose Y:=real_norm_metric_space hN.
pose jet:=fun alpha:M=>(@AnalyticGermJets.value R X NX hNX a m alpha:Y).
have hJet:continuous jet:=@analytic_germ_jet_continuous R X NX hNX a m.
have hEquation:(fun alpha:M=>@AnalyticGermJets.value R X NX hNX a m
    (@AnalyticGerms.opp R X NX hNX a alpha))=(fun alpha:M=>(-1:R)*:jet alpha).
  apply:funext=>alpha;rewrite scaleN1r;exact:analytic_germ_jet_negate.
rewrite hEquation=>alpha W hW.
exact:(hJet alpha _ (@real_norm_metric_scale_continuous R Z N hN (-1) (jet alpha) W hW)).
Qed.
