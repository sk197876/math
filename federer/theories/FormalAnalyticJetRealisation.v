(** Federer (1969), 3.4.5, p. 319: every
    symmetric coefficient sequence satisfying the original factorial
    bound is realised by an actual analytic germ. The proof
    uses the homogeneous series of 3.1.24, pp. 238–239. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology constructive_ereal.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP NormDifferentialUP
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  NormHigherDifferentialUP NormHigherDifferentialLocal NormHigherDifferentialUnique
  NormOpenDomainLaws ScalarNormMetricCompleteness NormSequenceConvergence NormSequenceLimitUnique
  SymmetricForms SymmetricOperatorNorm NormAnalyticUP
  AnalyticGermRepresentatives AnalyticGermUP AnalyticGermJetsUP AnalyticGermJetsSealed
  FormalAnalyticJetUP FormalAnalyticJetForms AnalyticJetMajorant AnalyticFormSeries AnalyticFormSeriesOrigin.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [formal_analytic_jet_realisation]: the
    realisation needed to prove compactness of the original
    growth classes, 3.4.5, p. 319. Actual symmetry
    and the printed factorial bounds are the only coefficient
    hypotheses. No analytic realisation is assumed. *)
Theorem formal_analytic_jet_realisation (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) s t
    (w:forall m,@ContinuousMultilinear.space R m X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R)):
  is_formal_analytic_jet s t w ->exists alpha:analytic_germ_space hNX a,
    forall m,@AnalyticGermJets.value R X NX hNX a m alpha=w m.
Proof.
move=>hw.
pose NS:=fun z:R^o=>`|z|.
pose hNS:=@scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i X R^o NX NS hNX hNS.
pose ev i:=@ContinuousMultilinear.evaluation R i X R^o NX NS hNX hNS.
pose ZN i:=@ContinuousMultilinear.norm R i X R^o NX NS hNX hNS.
have hZ i:is_continuous_multilinear_space NX NS (ev i) (ZN i).
  exact:ContinuousMultilinear.laws.
pose hZN i:=continuous_multilinear_norm_is_norm hNS (hZ i).
have [phi [hPhi [hPhiBound hPhiNorm]]]:=@formal_analytic_jet_forms_exists R X NX hNX s t w hw.
pose c:=((s%:R+1)*(t%:R+1):R).
have hS:0<=(s%:R:R):=ler0n R s.
have hT:0<=(t%:R:R):=ler0n R t.
have hc:0<c by rewrite /c mulr_gt0 // addrC ltr_pwDl.
have hCoefficient m (hm:(1<=m)%N):
    (symmetric_operator_norm hNX.1 NS (phi m)<=(c^+m*(m`!)%:R)%:E)%E.
  rewrite hPhiNorm lee_fin.
  apply:le_trans (@formal_analytic_jet_growth R X NX hNX s t w hw m) _.
  exact:(@analytic_factorial_growth_majorant R s%:R t%:R m hS hT hm).
have [r [hr [f [hf [E [G [hEval [hActual hLimits]]]]]]]]:=
  @bounded_analytic_form_series_exists R X R^o NX NS hNX hNS
    (@scalar_norm_metric_complete R) phi a c hc hPhiBound hCoefficient.
have hPhiEval i (u:{ffun 'I_i->X}):phi i [tuple u j | j<i]=ev i u (w i).
  rewrite hPhi;congr ((ev i) _ (w i));apply/ffunP=>j;by rewrite !ffunE tnth_mktuple.
have ha:NX (a-a)<r by rewrite subrr (real_seminorm_zero hNX.1).
have hOrigin i:G i a=w i.
  apply:(@norm_sequence_limit_unique R (Z i) (ZN i) (hZN i)
    (fun N=>\sum_(m<N) E m i a)).
  - exact:((@norm_sequence_convergence_epsilon R (Z i) (ZN i) (hZN i) _ _).1 (hLimits i a ha)).
  - move=>epsilon hEpsilon;exists i.+1=>N hN.
    have hSum:=@analytic_form_series_centre_prefix R X R^o NX NS hNX hNS phi w a E hPhiEval hEval i N hN.
    by rewrite hSum subrr (real_seminorm_zero (hZN i).1).
pose p:@analytic_representative_type R X NX hNX a:=exist _ f hf.
exists (analytic_germ p)=>i.
have hJet:=@AnalyticGermJets.laws R X NX hNX a i (analytic_germ p) p (erefl _).
have hOpen x (hx:NX (x-a)<r):norm_domain_interior NX (fun y=>NX (y-a)<r) x.
  exact:(@norm_open_ball_domain_interior R X NX hNX a r x hx).
have hGlobal:has_norm_higher_differential NX ev ZN setT f i a (G i a).
  exact:((@norm_higher_differential_open_restriction R X R^o NX NS hNX hNS Z ev ZN hZ
    i setT (fun y=>NX (y-a)<r) f (fun x hx=>Logic.I) hOpen a ha (G i a)).2 (hActual i a ha)).
rewrite -hOrigin.
exact:(@norm_higher_differential_unique R X R^o NX NS hNX hNS Z ev ZN hZ
  setT f i a _ _ hJet hGlobal).
Qed.
