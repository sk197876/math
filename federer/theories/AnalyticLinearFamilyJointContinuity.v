(** Federer (1969), 3.4.8(5), p. 328:
    actual linear pullback is jointly continuous in the
    germ and the linear map. The exact derivative rule,
    joint multilinear evaluation and finite source coordinates
    prove continuity for the original derivative metric. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  AnalyticGermUP AnalyticGermJetsSealed AnalyticGermMetric
  AnalyticGermJetContinuity AnalyticGermMetricTopology PointedAnalyticPullbackUP
  PointedAnalyticLinearPullbackJets FiniteMultilinearContinuity MultilinearEvaluationContinuity
  TopologicalProductMaps ScalarNormExtendedEmbedding.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_linear_family_pullback_jointly_continuous]:
    joint continuity used in 3.4.8(5), p. 328.
    The source basis is finite; no target basis, completeness,
    uniform germ-growth bound or conclusion of continuity is
    added to the independent pullback law. *)
Theorem analytic_linear_family_pullback_jointly_continuous
    (R:realType) (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (a:X) (b:Y)
    n (e:'I_n->X) (he:is_basis e) (U:topologicalType)
    (L:U->Hom X Y)
    (P:U->analytic_germ_space hNY b->analytic_germ_space hNX a):
  (forall t:U,is_pointed_analytic_germ_pullback (L t) (P t)) ->
  (forall t:U,L t a=b) ->
  (forall x:X,continuous (fun t:U=>(L t x:real_norm_metric_space hNY))) ->
  continuous (fun p:(@analytic_germ_metric R Y NY hNY b)*U=>
    (P p.2 p.1:@analytic_germ_metric R X NX hNX a)).
Proof.
move=>hP hBase hL.
pose N:=fun r:R^o=>`|r|.
pose hN:=@scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i X R^o NX N hNX hN.
pose ez i:=@ContinuousMultilinear.evaluation R i X R^o NX N hNX hN.
pose NZ i:=@ContinuousMultilinear.norm R i X R^o NX N hNX hN.
pose W i:=@ContinuousMultilinear.space R i Y R^o NY N hNY hN.
pose ew i:=@ContinuousMultilinear.evaluation R i Y R^o NY N hNY hN.
pose NW i:=@ContinuousMultilinear.norm R i Y R^o NY N hNY hN.
pose hW i:=@ContinuousMultilinear.laws R i Y R^o NY N hNY hN.
pose MY:=@analytic_germ_metric R Y NY hNY b.
pose T:=(MY*U)%type.
apply:(@analytic_germ_continuous_from_jets R X NX hNX a T _)=>m.
apply:(@finite_multilinear_continuous_from_basis_values R X NX hNX n e he m T _)=>l.
have hEquation:
  (fun p:T=>(ez m [ffun i=>e (l i)]
    (@AnalyticGermJets.value R X NX hNX a m (P p.2 p.1)):R^o))=
  (fun p:T=>(ew m [ffun i=>L p.2 (e (l i))]
    (@AnalyticGermJets.value R Y NY hNY b m p.1):R^o)).
  apply:funext=>p.
  have hJets:=@pointed_analytic_linear_pullback_jets R X Y NX NY hNX hNY a b
    (L p.2) (P p.2) (hP p.2) (hBase p.2) m p.1 [ffun i=>e (l i)].
  have hArgs:[ffun i=>L p.2 ([ffun j=>e (l j)] i)]=[ffun i=>L p.2 (e (l i))].
    by apply/ffunP=>i;rewrite !ffunE.
  by rewrite hArgs in hJets.
rewrite hEquation.
have hD:continuous (fun p:T=>(@AnalyticGermJets.value R Y NY hNY b m p.1:
    real_norm_metric_space (continuous_multilinear_norm_is_norm hN (hW m)))).
  move=>p;exact:(continuous_comp (@first_projection_continuous MY U p)
    (@analytic_germ_jet_continuous R Y NY hNY b m p.1)).
have hArguments i:continuous (fun p:T=>(L p.2 (e (l i)):real_norm_metric_space hNY)).
  move=>p;exact:(continuous_comp (@second_projection_continuous MY U p) (hL (e (l i)) p.2)).
have hArgumentsFFun i:continuous (fun p:T=>([ffun j=>L p.2 (e (l j))] i:real_norm_metric_space hNY)).
  have hEqual:(fun p:T=>[ffun j=>L p.2 (e (l j))] i)=(fun p:T=>L p.2 (e (l i))).
    by apply:funext=>p;rewrite ffunE.
  rewrite hEqual;exact:hArguments.
have hEvaluation:=@multilinear_evaluation_continuous_factors R Y R^o NY N hNY hN W ew NW hW T m
  (fun p:T=>@AnalyticGermJets.value R Y NY hNY b m p.1)
  (fun p:T=>[ffun i=>L p.2 (e (l i))]) hD hArgumentsFFun.
have hScalar:continuous (fun r:real_norm_metric_space hN=>(r:R^o)).
  exact:(@scalar_norm_real_identity_continuous R).
move=>p;exact:(continuous_comp (hEvaluation p) (hScalar _)).
Qed.
