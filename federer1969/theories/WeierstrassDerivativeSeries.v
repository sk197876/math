(** Federer (1969), 3.4.6, pp. 322–323: the
    original Taylor forms give an actual analytic germ
    and every shifted derivative-series limit on one
    positive-radius neighbourhood. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets topology constructive_ereal.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP NormDifferentialUP NormOpenDomainLaws
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  NormHigherDifferentialUP NormHigherDifferentialLocal NormHigherDifferentialUnique
  NormSequenceConvergence NormSequenceLimitUnique ScalarNormMetricCompleteness
  SymmetricForms SymmetricOperatorNorm PolynomialTaylorTerms AnalyticJetMajorant
  AnalyticGermRepresentatives AnalyticGermUP AnalyticGermJetsSealed AnalyticGermTaylorInjective
  AnalyticGermCoefficientForms AnalyticGermGrowthUP AnalyticGermGrowthSealed AnalyticGermGrowthCover
  AnalyticFormSeries AnalyticFormSeriesOrigin.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weierstrass_all_derivative_series]:
    the displayed Taylor expansions of all original higher
    derivatives in 3.4.6, pp. 322–323, converge
    to actual derivatives on one neighbourhood. The
    project's proved normal homogeneous-series theorem
    supplies the function and every derivative limit.
    Every form is the original germ jet, rather than
    an assumed analytic or formal quotient. *)
Theorem weierstrass_all_derivative_series (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (alpha:analytic_germ_space hNX (0:X)):
  exists phi:forall m,S_m X R^o m,
    (forall m t,phi m t=@ContinuousMultilinear.evaluation R m X R^o NX (fun r=>`|r|)
      hNX (@scalar_absolute_value_norm R) [ffun i=>tnth t i] (@AnalyticGermJets.value R X NX hNX 0 m alpha)) /\
    exists r:R,0<r /\exists f:analytic_representative_type hNX (0:X),analytic_germ f=alpha /\
    exists E:forall m i,X->@ContinuousMultilinear.space R i X R^o NX (fun r=>`|r|) hNX (@scalar_absolute_value_norm R),
    exists G:forall i,X->@ContinuousMultilinear.space R i X R^o NX (fun r=>`|r|) hNX (@scalar_absolute_value_norm R),
      (forall m i x u,@ContinuousMultilinear.evaluation R i X R^o NX (fun r=>`|r|) hNX (@scalar_absolute_value_norm R)
        u (E m i x)=symmetric_taylor_term i (phi m) x [tuple u j | j<i]) /\
      (forall i x,NX x<r ->has_norm_higher_differential NX
        (fun j=>@ContinuousMultilinear.evaluation R j X R^o NX (fun r=>`|r|) hNX (@scalar_absolute_value_norm R))
        (fun j=>@ContinuousMultilinear.norm R j X R^o NX (fun r=>`|r|) hNX (@scalar_absolute_value_norm R))
        (fun y=>NX y<r) (analytic_representative_value f) i x (G i x)) /\
      forall i x,NX x<r ->forall epsilon:R,0<epsilon ->exists n:nat,forall M,(n<=M)%N ->
        @ContinuousMultilinear.norm R i X R^o NX (fun r=>`|r|) hNX (@scalar_absolute_value_norm R)
          (\sum_(m<M) E m i x-G i x)<epsilon.
Proof.
pose N:=fun r:R^o=>`|r|.
pose hN:=@scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i X R^o NX N hNX hN.
pose ev i:=@ContinuousMultilinear.evaluation R i X R^o NX N hNX hN.
pose NZ i:=@ContinuousMultilinear.norm R i X R^o NX N hNX hN.
pose hZ i:=@ContinuousMultilinear.laws R i X R^o NX N hNX hN.
pose hNZ i:=continuous_multilinear_norm_is_norm hN (hZ i).
have [phi [hPhi [hBound hNorm]]]:=@analytic_germ_coefficient_forms_exists R X NX hNX 0 alpha.
have [s [t [_ [_ hGrowth]]]]:=@analytic_germ_positive_growth_cover R X NX hNX 0 alpha.
pose c:=((s%:R+1)*(t%:R+1):R).
have hS:0<=(s%:R:R):=ler0n R s.
have hT:0<=(t%:R:R):=ler0n R t.
have hc:0<c by rewrite /c mulr_gt0 // addrC ltr_pwDl.
have hCoefficient m (hm:(1<=m)%N):
    (symmetric_operator_norm hNX.1 N (phi m)<=(c^+m*(m`!)%:R)%:E)%E.
  rewrite hNorm lee_fin.
  have hActual:=((analytic_germ_growth_membership (@AnalyticGermGrowth.laws R X NX hNX 0 s t) alpha).1 hGrowth m).
  apply:le_trans hActual _.
  exact:(@analytic_factorial_growth_majorant R s%:R t%:R m hS hT hm).
have [r [hr [F [hF [E [G [hEval [hActual hLimit]]]]]]]]:=@bounded_analytic_form_series_exists R X R^o NX N hNX hN
  (@scalar_norm_metric_complete R) phi 0 c hc hBound hCoefficient.
have hPhiEval i (u:{ffun 'I_i->X}):phi i [tuple u j | j<i]=ev i u (@AnalyticGermJets.value R X NX hNX 0 i alpha).
  rewrite hPhi;congr (ev i _ _);apply/ffunP=>j;by rewrite !ffunE tnth_mktuple.
have ha:NX (0-0)<r by rewrite subrr (real_seminorm_zero hNX.1).
have hOrigin i:G i 0=@AnalyticGermJets.value R X NX hNX 0 i alpha.
  apply:(@norm_sequence_limit_unique R (Z i) (NZ i) (hNZ i) (fun M=>\sum_(m<M) E m i 0)).
  - exact:((@norm_sequence_convergence_epsilon R (Z i) (NZ i) (hNZ i) _ _).1 (hLimit i 0 ha)).
  - move=>epsilon hEpsilon;exists i.+1=>M hM.
    have hSum:=@analytic_form_series_centre_prefix R X R^o NX N hNX hN phi
      (fun i=>@AnalyticGermJets.value R X NX hNX 0 i alpha) 0 E hPhiEval hEval i M hM.
    rewrite hSum subrr.
    have hZero:NZ i 0=0:=real_seminorm_zero (hNZ i).1.
    by rewrite hZero.
pose f:analytic_representative_type hNX (0:X):=exist _ F hF.
have hRep:analytic_germ f=alpha.
  apply:(@analytic_germ_jets_injective R X NX hNX 0)=>i.
  have hOpen x (hx:NX (x-0)<r):norm_domain_interior NX (fun y=>NX (y-0)<r) x.
    exact:(@norm_open_ball_domain_interior R X NX hNX 0 r x hx).
  have hFull:=(@norm_higher_differential_open_restriction R X R^o NX N hNX hN Z ev NZ hZ
    i setT (fun y=>NX (y-0)<r) F (fun x _=>Logic.I) hOpen 0 ha (G i 0)).2 (hActual i 0 ha).
  rewrite -hOrigin.
  exact:(@norm_higher_differential_unique R X R^o NX N hNX hN Z ev NZ hZ setT F i 0 _ _
    (@AnalyticGermJets.laws R X NX hNX 0 i (analytic_germ f) f (erefl _)) hFull).
exists phi;split;first exact:hPhi.
exists r;split;first exact:hr.
exists f;split;first exact:hRep.
exists E,G;split.
- move=>m i x u;have hh:=hEval m i x u;by rewrite subr0 in hh.
split.
- move=>i x hx.
  have hDomain:(fun y:X=>is_true (NX (y-0)<r))=(fun y:X=>is_true (NX y<r)).
    apply:funext=>y;by rewrite subr0.
  have hh:=hActual i x;rewrite subr0 hDomain in hh;exact:hh hx.
- move=>i x hx epsilon hEpsilon.
  have hRaw:=hLimit i x;rewrite subr0 in hRaw.
  have hEpsilonLimit:=(@norm_sequence_convergence_epsilon R (Z i) (NZ i) (hNZ i) _ _).1 (hRaw hx).
  exact:hEpsilonLimit epsilon hEpsilon.
Qed.
