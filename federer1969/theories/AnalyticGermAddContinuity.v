(** Federer (1969), 3.4.5, p. 319: addition
    is continuous for the original derivative-series germ metric.
    The proof uses actual derivative additivity and the proved
    finite-coordinate topology criterion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormMetricContinuity NormMetricSubtractContinuity
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  AnalyticGermUP AnalyticGermSealed AnalyticGermJetsSealed AnalyticGermJetArithmetic
  AnalyticGermMetric AnalyticGermJetContinuity AnalyticGermMetricTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_germ_add_continuous]: continuity
    of addition among the ring operations in 3.4.5,
    p. 319. Neither finite dimension nor completeness
    is needed for this implication. *)
Theorem analytic_germ_add_continuous (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X):
  continuous (fun p:(@analytic_germ_metric R X NX hNX a)*(@analytic_germ_metric R X NX hNX a)=>
    (@AnalyticGerms.add R X NX hNX a p.1 p.2:@analytic_germ_metric R X NX hNX a)).
Proof.
pose M:=@analytic_germ_metric R X NX hNX a.
apply:(@analytic_germ_continuous_from_jets R X NX hNX a [the topologicalType of (M*M)%type] _)=>m.
pose Z:=@ContinuousMultilinear.space R m X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R).
pose N:=@ContinuousMultilinear.norm R m X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R).
pose hN:=continuous_multilinear_norm_is_norm (@scalar_absolute_value_norm R)
  (@ContinuousMultilinear.laws R m X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R)).
pose Y:=real_norm_metric_space hN.
pose jet:=fun alpha:M=>(@AnalyticGermJets.value R X NX hNX a m alpha:Y).
have hJet:continuous jet:=@analytic_germ_jet_continuous R X NX hNX a m.
have hPair:=@continuous_product_maps [the topologicalType of M] [the topologicalType of M]
  [the topologicalType of Y] [the topologicalType of Y] jet jet hJet hJet.
have hEquation:(fun p:M*M=>@AnalyticGermJets.value R X NX hNX a m
    (@AnalyticGerms.add R X NX hNX a p.1 p.2))=(fun p:M*M=>jet p.1+jet p.2).
  apply:funext=>p;exact:analytic_germ_jet_add.
rewrite hEquation=>p W hW.
exact:(hPair p _ (@real_norm_metric_add_continuous R Z N hN (jet p.1,jet p.2) W hW)).
Qed.
