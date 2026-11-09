(** Federer (1969), 3.4.5, p. 319: the analytic
    ring is the union of its positive-integer factorial-growth classes. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormRegularity NormHigherDifferentialUP NormHigherDifferentialLocal
  ContinuousMultilinearUP ContinuousMultilinearSealed NormAnalyticUP NormAnalyticBoundNonnegative
  AnalyticGermUP AnalyticGermRepresentatives AnalyticGermRingLaws AnalyticGermJetsUP AnalyticGermJetsSealed
  AnalyticGermGrowthUP AnalyticGermGrowthSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_germ_positive_growth_cover]: every
    original analytic germ belongs to a displayed class with
    positive integer s and t, 3.4.5, p. 319.
    Archimedean integer bounds absorb the local analytic constant
    and the actual zeroth derivative separately. *)
Theorem analytic_germ_positive_growth_cover (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) (alpha:analytic_germ_space hNX a):
  exists s t:nat,(1<=s)%N /\(1<=t)%N /\@AnalyticGermGrowth.value R X NX hNX a s t alpha.
Proof.
pose NS:=fun t:R^o=>`|t|.
pose hNS:=@scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i X R^o NX NS hNX hNS.
pose ev i:=@ContinuousMultilinear.evaluation R i X R^o NX NS hNX hNS.
pose ZN i:=@ContinuousMultilinear.norm R i X R^o NX NS hNX hNS.
have hZ i:is_continuous_multilinear_space NX NS (ev i) (ZN i).
  exact:ContinuousMultilinear.laws.
have [f hf]:=@analytic_germ_has_representative R X NX hNX a alpha.
have [U [c [ha [hUT [hClass hBound]]]]]:=analytic_representative_analytic f.
have hc:=norm_analytic_operator_witness_nonnegative ha hClass hBound.
pose d0:=@analytic_germ_jet_norm R X NX hNX a 0 alpha.
pose s:=(Num.bound `|d0|).+1.
pose t:=(Num.bound c).+1.
have hS:(1<=s)%N by rewrite /s.
have hT:(1<=t)%N by rewrite /t.
have hSOne:(1:R)<=s%:R by rewrite ler1n.
have hZero:d0<=s%:R.
  apply:le_trans (ler_norm d0) _.
  apply:le_trans (ltW (archi_boundP (normr_ge0 d0))) _.
  by rewrite /s ler_nat leqnSn.
have hC:c<=t%:R.
  apply:le_trans (ltW (archi_boundP hc)) _.
  by rewrite /t ler_nat leqnSn.
exists s,t;split;first exact:hS.
split;first exact:hT.
apply/(@analytic_germ_growth_membership R X NX hNX a s t _ (@AnalyticGermGrowth.laws R X NX hNX a s t) alpha).
move=>[|m].
- rewrite expr0 mulr1 /= mulr1;exact:hZero.
- have hOpen x (hx:U x):NormDifferentialUP.norm_domain_interior NX U x:=((hClass 0%N).1 x hx).1.
  pose z:=@AnalyticGermJets.value R X NX hNX a m.+1 alpha.
  have hFull:=@AnalyticGermJets.laws R X NX hNX a m.+1 alpha f hf.
  have hLocal:=(@norm_higher_differential_open_restriction R X R^o NX NS hNX hNS Z ev ZN hZ
    m.+1 setT U (analytic_representative_value f) hUT hOpen a ha z).1 hFull.
  have hOriginal:=hBound m.+1 (leq0n m) a ha z hLocal.
  have hPower:=lerXn2r m.+1 hc (ler0n R t) hC.
  have hFact:0<=(((m.+1)`!)%:R:R) by rewrite ler0n.
  have hFirst:=le_trans hOriginal (ler_wpM2r hFact hPower).
  have hNonnegative:0<=(t%:R^+m.+1*((m.+1)`!)%:R:R) by rewrite mulr_ge0 // exprn_ge0 // ler0n.
  have hLast:=ler_wpM2r hNonnegative hSOne.
  rewrite mul1r mulrA in hLast.
  exact:le_trans hFirst hLast.
Qed.
