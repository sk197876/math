(** Federer (1969), 3.4.5, p. 319: all actual
    derivatives at the centre determine an analytic germ,
    ensuring that the displayed jet distance separates germs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity NormClassZeroTopology
  NormHigherDifferentialUP NormHigherDifferentialLocal NormHigherDifferentialUnique
  ContinuousMultilinearUP ContinuousMultilinearSealed NormAnalyticUP NormAnalyticDiagonal NormAnalyticTaylor
  LocalGermUP LocalGermSealed AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRingLaws
  AnalyticGermJetsUP AnalyticGermJetsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_germ_jets_injective]: the metric
    definiteness implicit in 3.4.5, p. 319, by
    the uniformly convergent actual Taylor expansions of 3.1.24.
    No formal-series identity or Taylor uniqueness is assumed. *)
Theorem analytic_germ_jets_injective (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (alpha beta:analytic_germ_space hNX a):
  (forall m,@AnalyticGermJets.value R X NX hNX a m alpha=
    @AnalyticGermJets.value R X NX hNX a m beta) ->alpha=beta.
Proof.
move=>hJets.
pose NS:=fun t:R^o=>`|t|.
pose hNS:=@scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i X R^o NX NS hNX hNS.
pose ev i:=@ContinuousMultilinear.evaluation R i X R^o NX NS hNX hNS.
pose ZN i:=@ContinuousMultilinear.norm R i X R^o NX NS hNX hNS.
have hZ i:is_continuous_multilinear_space NX NS (ev i) (ZN i).
  exact:ContinuousMultilinear.laws.
pose P:=@analytic_representative_type R X NX hNX a.
pose value:=@analytic_representative_value R X NX hNX a.
pose germ:=@analytic_germ R X NX hNX a.
have hG:=@LocalGerms.laws (Topological.clone (real_norm_metric_space hNX) _) R P value a.
have [f hf]:=@analytic_germ_has_representative R X NX hNX a alpha.
have [g hg]:=@analytic_germ_has_representative R X NX hNX a beta.
have hTF:=@norm_diagonal_analytic_taylor R X R^o NX NS hNX hNS setT (value f) a
  (@norm_analytic_diagonal R X R^o NX NS hNX hNS setT (value f) a (analytic_representative_analytic f)).
have hTG:=@norm_diagonal_analytic_taylor R X R^o NX NS hNX hNS setT (value g) a
  (@norm_analytic_diagonal R X R^o NX NS hNX hNS setT (value g) a (analytic_representative_analytic g)).
have [U [haU [hUT [hClassF [F [hF hLimitF]]]]]]:=hTF.
have [V [haV [hVT [hClassG [H [hH hLimitG]]]]]]:=hTG.
have hU x (hx:U x):norm_domain_interior NX U x:=((hClassF 0%N).1 x hx).1.
have hV x (hx:V x):norm_domain_interior NX V x:=((hClassG 0%N).1 x hx).1.
have hEqual m:F m=H m.
  have hFullF:=(@norm_higher_differential_open_restriction R X R^o NX NS hNX hNS Z ev ZN hZ
    m setT U (value f) hUT hU a haU (F m)).2 (hF m).
  have hFullH:=(@norm_higher_differential_open_restriction R X R^o NX NS hNX hNS Z ev ZN hZ
    m setT V (value g) hVT hV a haV (H m)).2 (hH m).
  have hJetF:=@AnalyticGermJets.laws R X NX hNX a m alpha f hf.
  have hJetG:=@AnalyticGermJets.laws R X NX hNX a m beta g hg.
  have hFEq:=@norm_higher_differential_unique R X R^o NX NS hNX hNS Z ev ZN hZ
    setT (value f) m a _ _ hFullF hJetF.
  have hGEq:=@norm_higher_differential_unique R X R^o NX NS hNX hNS Z ev ZN hZ
    setT (value g) m a _ _ hFullH hJetG.
  by rewrite hFEq hGEq hJets.
have hSum N x:(\sum_(m<N.+1) (m`!)%:R^-1*:ev m [ffun i=>x-a] (F m))=
    (\sum_(m<N.+1) (m`!)%:R^-1*:ev m [ffun i=>x-a] (H m)).
  apply:eq_bigr=>m _;by rewrite hEqual.
rewrite -hf -hg;apply/(local_germ_equality hG).
exists (U `&` V);split.
- apply:openI.
  + exact:(@norm_class_zero_domain_open R X R^o NX NS hNX U (value f)
      (norm_class_continuous (hClassF 0%N))).
  + exact:(@norm_class_zero_domain_open R X R^o NX NS hNX V (value g)
      (norm_class_continuous (hClassG 0%N))).
- split;first by split.
  move=>x [hx hy];apply/eqP;rewrite -subr_eq0;apply/eqP;apply:hNS.2.
  apply/eqP;rewrite eq_le (real_seminorm_nonnegative hNS.1) andbT leNgt.
  apply/negP=>hPositive.
  pose eps:=NS (value f x-value g x)/3.
  have hEps:0<eps by rewrite /eps divr_gt0 // ltr0n.
  have [nF hnF]:=hLimitF eps hEps.
  have [nG hnG]:=hLimitG eps hEps.
  pose n:=(nF+nG)%N.
  have hnFle:(nF<=n)%N by rewrite /n leq_addr.
  have hnGle:(nG<=n)%N by rewrite /n leq_addl.
  have hFirst:=hnF n hnFle x hx.
  have hSecond:=hnG n hnGle x hy.
  rewrite -(hSum n x) in hSecond.
  pose S:=\sum_(m<n.+1) (m`!)%:R^-1*:ev m [ffun i=>x-a] (F m).
  have hTriangle:=real_seminorm_triangle hNS.1 (value f x-S) (S-value g x).
  have hCancel:(value f x-S)+(S-value g x)=value f x-value g x by rewrite addrA subrK.
  rewrite hCancel (real_seminorm_subtract hNS.1 S (value g x)) in hTriangle.
  have hBoth:=ltrD hFirst hSecond.
  change (is_true (NS (value f x-S)+NS (value g x-S)<eps+eps)) in hBoth.
  have hSmall:=le_lt_trans hTriangle hBoth.
  rewrite /eps /NS in hSmall.
  clear - R hPositive hSmall.
  by lra.
Qed.
