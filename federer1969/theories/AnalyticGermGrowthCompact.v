(** Federer (1969), 3.4.5, p. 319: every
    original factorial-growth class of analytic germs is compact
    when the source has finite dimension. Actual homogeneous
    series realise the compact symmetric coefficient set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology fingroup perm.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm FiniteArgumentPermutation
  AnalyticGermUP AnalyticGermTaylorInjective AnalyticGermJetsSealed AnalyticGermMetric AnalyticGermJetSymmetry
  AnalyticGermGrowthUP AnalyticGermGrowthSealed FormalAnalyticJetUP FormalAnalyticJetRealisation
  JetCoefficientCompact JetSequenceMetricUP JetMetricFiniteControl.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_germ_growth_class_compact]: the
    compactness assertion in 3.4.5, p. 319.
    Finite-dimensional norm balls give a compact product of
    bounded symmetric derivative sequences. Actual realisation,
    the exact metric's finite-coordinate control and the
    continuous-image theorem give precisely the original class.
    No realisation or compactness conclusion is a hypothesis. *)
Theorem analytic_germ_growth_class_compact (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) n (b:'I_n->X) (hb:is_basis b) s t:
  @compact (@analytic_germ_metric R X NX hNX a)
    (@AnalyticGermGrowth.value R X NX hNX a s t).
Proof.
pose NS:=fun z:R^o=>`|z|.
pose hNS:=@scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i X R^o NX NS hNX hNS.
pose ev i:=@ContinuousMultilinear.evaluation R i X R^o NX NS hNX hNS.
pose N i:=@ContinuousMultilinear.norm R i X R^o NX NS hNX hNS.
pose hN i:=continuous_multilinear_norm_is_norm hNS
  (@ContinuousMultilinear.laws R i X R^o NX NS hNX hNS).
pose T i:=Topological.clone (real_norm_metric_space (hN i)) _.
pose P:=prod_topology T.
pose M:=@analytic_germ_metric R X NX hNX a.
pose jet:=@AnalyticGermJets.value R X NX hNX a.
pose d:=@analytic_germ_distance R X NX hNX a.
have hd:=@analytic_germ_distance_formula R X NX hNX a.
pose K:set P:=fun w=>(forall i,N i (w i)<=s%:R*t%:R^+i*(i`!)%:R) /\
  forall i (sigma:'S_i) u,ev i (finite_argument_permutation sigma u) (w i)=ev i u (w i).
have hK:compact K:=@bounded_symmetric_jet_coefficients_compact R X NX hNX n b hb s t.
have hex w:K w ->exists alpha:M,forall i,jet i alpha=w i.
  move=>hw;apply:(@formal_analytic_jet_realisation R X NX hNX a s t w).
  by split;[exact:hw.2|exact:hw.1].
pose pick (w:P):M:=if pselect (K w) is left h then projT1 (cid (hex w h))
  else @analytic_germ_zero R X NX hNX a.
have hp w (hw:K w):forall i,jet i (pick w)=w i.
  rewrite /pick;case:pselect=>[h|h];last by exfalso;exact:h hw.
  exact:(projT2 (cid (hex w h))).
have hContinuous:{within K,continuous pick}.
  apply/subspace_continuousP=>w hw U hU.
  have [epsilon hEpsilon hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP (pick w) U) hU.
  have [k [delta [hDelta hControl]]]:=@jet_metric_finite_coordinate_control R
    (analytic_germ_space hNX a) Z N hN jet d hd epsilon hEpsilon.
  have hNear (i:'I_k):nbhs w [set v:P|N i (w i-v i)<delta].
    have hBallN:nbhs (w i:T i) [set z:T i|N i (w i-z)<delta].
      apply:(proj2 (metricType_numDomainType.nbhs_mdistP (w i:T i) _)).
      exists delta;first exact:hDelta.
      by move=>z hz.
    exact:(@proj_continuous _ T i w _ hBallN).
  have hAll:=@filter_forall P (Finite.clone 'I_k _) _ (nbhs w) (nbhs_filter w) hNear.
  change (nbhs w [set v:P|K v ->U (pick v)]).
  apply:filterS hAll=>v hv hKv;apply:hBall.
  change (is_true (d (pick w) (pick v)<epsilon)).
  apply:hControl=>i hi;rewrite (hp w hw) (hp v hKv);exact:(hv (Ordinal hi)).
have hClasses:=@AnalyticGermGrowth.laws R X NX hNX a s t.
have hImage:pick @` K=(@AnalyticGermGrowth.value R X NX hNX a s t:set M).
  apply/seteqP;split.
  - move=>alpha [w hw <-];apply/(analytic_germ_growth_membership hClasses _)=>i.
    change (is_true (N i (jet i (pick w))<=s%:R*t%:R^+i*(i`!)%:R)).
    rewrite (hp w hw);exact:hw.1 i.
  - move=>alpha hAlpha.
    pose w:P:=fun i=>jet i alpha.
    have hw:K w.
      split;first exact:((analytic_germ_growth_membership hClasses alpha).1 hAlpha).
      move=>i sigma u;exact:(@analytic_germ_jet_symmetric R X NX hNX a i alpha sigma u).
    exists w;first exact:hw.
    apply:(@analytic_germ_jets_injective R X NX hNX a)=>i.
    exact:(hp w hw i).
rewrite -hImage;exact:(continuous_compact hContinuous hK).
Qed.
