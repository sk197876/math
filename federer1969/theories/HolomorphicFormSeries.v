(** Federer (1969), 3.4.12, p. 339:
    complex symmetric coefficients with the original factorial
    growth are realised by actual holomorphic germs.
    Reuse the normal-series realization, actual derivative limits
    and centre coefficient identification already proved for arbitrary
    real normed targets. Closed complex scalar equations supply
    the missing holomorphic condition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology constructive_ereal.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus
  ComplexScalarNorm ComplexScalarNormCompleteness SymmetricForms SymmetricOperatorNorm
  TensorFamilyUP FamilyUpdate MultilinearFamilyAlgebra PolynomialTaylorTerms
  ComplexSymmetricTaylorRestriction ContinuousSymmetricFormAdapter
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm ContinuousMultilinearOne
  NormDifferentialUP NormDifferentialLocal NormDifferentialDirectional NormBoundedLinearTopology
  NormHigherDifferentialUP NormHigherDifferentialFirst NormHigherDifferentialLocal NormHigherDifferentialUnique
  NormMetric NormSequenceConvergence NormSequenceLimitUnique NormOpenDomainLaws NormLinearDomainLaws
  NormAnalyticUP AnalyticGermNeighbourhood NormAnalyticOperations AnalyticFormSeries AnalyticFormSeriesOrigin
  ComplexScalarSlotUP ComplexMultilinearSlotsClosed HolomorphicUP
  HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermJetsUP HolomorphicGermJetsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Series.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:is_complex_norm NX.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation NC:=(@complex_modulus R).
Local Notation hNC:=(@complex_modulus_real_norm R).
Local Notation Z:=(fun k=>@ContinuousMultilinear.space R k XR CR NX NC hNXR hNC).
Local Notation ev:=(fun k=>@ContinuousMultilinear.evaluation R k XR CR NX NC hNXR hNC).
Local Notation ZN:=(fun k=>@ContinuousMultilinear.norm R k XR CR NX NC hNXR hNC).
Local Notation hZ:=(fun k=>@ContinuousMultilinear.laws R k XR CR NX NC hNXR hNC).
Local Notation hZN:=(fun k=>continuous_multilinear_norm_is_norm hNC (hZ k)).

(** Source for [holomorphic_form_series_realisation]: the
    actual analytic realization of complex coefficients required
    in 3.4.12, p. 339. Only the original
    coefficient equations and bounds are supplied. Holomorphy,
    existence of the sum, actual differentiation and all
    original germ coefficients are proved from these data. *)
Theorem holomorphic_form_series_realisation (F:forall m,S_m X C^o m)
    (P:forall m,S_m XR CR m) (a:X) (c:R):
  (forall m t,P m t=F m t) ->0<c ->
  (forall m,@norm_bounded_symmetric_form R m XR CR NX NC (P m)) ->
  (forall m,(1<=m)%N ->
    (@symmetric_operator_norm R XR CR NX hNXR.1 NC m (P m)<=(c^+m*(m`!)%:R)%:E)%E) ->
  exists alpha:holomorphic_germ_space hNXR a,forall m t,
    @ev m [ffun i=>tnth t i] (@HolomorphicGermJets.value R X NX hNXR a m alpha)=F m t.
Proof.
move=>hValues hc hBound hGrowth.
have [r [hr [f [hAnalytic [E [D [hEval [hActual hLimits]]]]]]]]:=
  @bounded_analytic_form_series_exists R XR CR NX NC hNXR hNC
    (@complex_scalar_norm_complete R) P a c hc hBound hGrowth.
have hSlot m i x:has_complex_scalar_slot_laws (fun u=>@ev i u (E m i x)).
  move=>u j z v.
  rewrite !hEval !(complex_symmetric_taylor_restriction (hValues m)).
  exact:(@multilinear_family_scale C i (fun _=>X) C^o
    (fun u=>symmetric_taylor_term i (F m) (x-a) [tuple u l | l<i])
    (sform_finite_family_multilinear (symmetric_taylor_term i (F m) (x-a)))
    u j z v).
have hPartial i N x:has_complex_scalar_slot_laws
    (fun u=>@ev i u (\sum_(m<N) E m i x)).
  move=>u j z v.
  have hSum (w:{ffun 'I_i->X}):@ev i w (\sum_(m<N) E m i x)=
      \sum_(m<N) @ev i w (E m i x).
    exact:linear_sum.
  rewrite !hSum scaler_sumr;apply:eq_bigr=>m _;exact:hSlot m i x u j z v.
have hDSlot i x (hx:NX (x-a)<r):has_complex_scalar_slot_laws (fun u=>@ev i u (D i x)).
  have hLimit:=@complex_multilinear_slots_limit R X C^o NX NC hNX
    (@complex_modulus_complex_norm R) i (Z i) (@ev i) (@ZN i) (hZ i).
  have hProof:(complex_norm_real (@complex_modulus_complex_norm R))=hNC:=Prop_irrelevance _ _.
  rewrite hProof in hLimit.
  exact:(hLimit (fun N=>\sum_(m<N) E m i x) (D i x) (fun N=>hPartial i N x) (hLimits i x hx)).
have [V [haV [hVT [hV hAnalyticV]]]]:=analytic_germ_open_representative hAnalytic.
pose U:=fun x=>V x /\NX (x-a)<r.
have haU:U a by rewrite /U subrr (real_seminorm_zero hNXR.1);split.
have hOpen x (hx:U x):@norm_domain_interior R XR NX U x.
  apply:norm_domain_intersection_interior.
  - have hVN:=hV;rewrite openE in hVN.
    exact:((@norm_domain_interior_neighbourhood R XR NX hNXR V x).2 (hVN x hx.1)).
  - exact:(@norm_open_ball_domain_interior R XR NX hNXR a r x hx.2).
have hHolomorphic:@is_holomorphic R X C^o NX NC hNXR hNC U f.
  split.
  - exact:(@norm_analytic_open_restriction R XR CR NX NC hNXR hNC V U f
      (fun x hx=>hx.1) hOpen hAnalyticV).
  - move=>x L hx hL.
    have hFirst:=(@norm_higher_differential_first R XR CR NX NC hNXR hNC
      Z ev ZN hZ (fun y=>NX (y-a)<r) f x (D 1%N x)).1 (hActual 1%N x hx.2).
    have hFirstU:=@norm_differential_restrict R XR CR NX NC
      (fun y=>NX (y-a)<r) U f x _ (fun y hy=>hy.2) (hOpen x hx) hFirst.
    have hEqual:=norm_differential_unique hNXR hNC hL hFirstU.
    move=>z v;rewrite hEqual.
    change (@ev 1%N [ffun _=>z*:(v:X)] (D 1%N x)=
      z*:(@ev 1%N [ffun _=>v] (D 1%N x):C^o)).
    have hScalar:=hDSlot 1%N x hx.2 [ffun _=>0] ord0 z v.
    by rewrite !one_arity_replace in hScalar.
pose p:@holomorphic_representative_type R X NX hNXR a:=exist _ f (ex_intro _ U (conj haU hHolomorphic)).
have hRepresent m:exists w:Z m,forall u,@ev m u w = P m [tuple u i | i<m].
  apply:(@continuous_symmetric_form_representation R m XR CR (Z m) NX NC (@ev m) (@ZN m) (hZ m) (P m)).
  exact:hBound m.
pose w m:=projT1 (cid (hRepresent m)).
have hW m:=projT2 (cid (hRepresent m)).
have hPhiEval m (u:{ffun 'I_m->X}):P m [tuple u i | i<m]=@ev m u (w m).
  exact:esym (hW m u).
have haBall:NX (a-a)<r by rewrite subrr (real_seminorm_zero hNXR.1).
have hOrigin m:D m a=w m.
  apply:(@norm_sequence_limit_unique R (Z m) (@ZN m) (hZN m)
    (fun N=>\sum_(j<N) E j m a)).
  - exact:((@norm_sequence_convergence_epsilon R (Z m) (@ZN m) (hZN m) _ _).1 (hLimits m a haBall)).
  - move=>epsilon hEpsilon;exists m.+1=>N hN.
    have hSum:=@analytic_form_series_centre_prefix R XR CR NX NC hNXR hNC P w a E
      hPhiEval hEval m N hN.
    by rewrite hSum subrr (real_seminorm_zero (hZN m).1).
exists (holomorphic_germ p)=>m t.
have hJet:=@HolomorphicGermJets.laws R X NX hNXR a m (holomorphic_germ p) p (erefl _).
have hBallOpen x (hx:NX (x-a)<r):@norm_domain_interior R XR NX (fun y=>NX (y-a)<r) x.
  exact:(@norm_open_ball_domain_interior R XR NX hNXR a r x hx).
have hFull:=(@norm_higher_differential_open_restriction R XR CR NX NC hNXR hNC
  Z ev ZN hZ m setT (fun y=>NX (y-a)<r) f (fun x _=>Logic.I) hBallOpen a haBall (D m a)).2
  (hActual m a haBall).
have hEqual:=@norm_higher_differential_unique R XR CR NX NC hNXR hNC Z ev ZN hZ
  setT f m a _ _ hJet hFull.
rewrite hEqual hOrigin hW hValues.
congr (F m _);apply:eq_from_tnth=>i;by rewrite tnth_mktuple ffunE.
Qed.
End Series.
