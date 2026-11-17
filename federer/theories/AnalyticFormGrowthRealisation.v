(** Supporting Federer (1969), 3.4.8(5), p. 328:
    symmetric coefficient forms with real factorial-growth
    bounds have actual analytic germs. This expands
    the coefficient realisation of 3.4.5, p. 319,
    using the already proved integer-growth theorem.
    Integer bounds serve only as local existence witnesses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal fingroup perm.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearSymmetricNorm ContinuousSymmetricFormAdapter SymmetricForms SymmetricOperatorNorm
  AnalyticGermUP AnalyticGermRing AnalyticGermJetsSealed FormalAnalyticJetUP FormalAnalyticJetRealisation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_form_growth_realisation]: real
    growth constants are absorbed into integer bounds
    and the original analytic realisation theorem applies.
    The resulting derivatives are the actual prescribed
    forms, supporting 3.4.8(5), p. 328, from
    the construction proved for 3.4.5, p. 319. *)
Theorem analytic_form_growth_realisation (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) a (phi:forall m,S_m X R^o m) (S T:R):
  0<=S ->0<=T ->
  (forall m,(symmetric_operator_norm hNX.1 (fun z:R^o=>`|z|%R) (phi m)
    <=(S*T^+m*(m`!)%:R)%:E)%E) ->
  exists alpha:@analytic_germ_ring R X NX hNX a,forall m u,
    @ContinuousMultilinear.evaluation R m X R^o NX (fun z=>`|z|%R) hNX (@scalar_absolute_value_norm R)
      u (@AnalyticGermJets.value R X NX hNX a m alpha) = phi m [tuple u i | i<m].
Proof.
move=>hS hT hBound.
pose NS:=fun z:R^o=>`|z|%R.
pose hNS:=@scalar_absolute_value_norm R.
pose Z:=fun m=>@ContinuousMultilinear.space R m X R^o NX NS hNX hNS.
pose ev:=fun m=>@ContinuousMultilinear.evaluation R m X R^o NX NS hNX hNS.
pose N:=fun m=>@ContinuousMultilinear.norm R m X R^o NX NS hNX hNS.
have hZ m:=@ContinuousMultilinear.laws R m X R^o NX NS hNX hNS.
have hPhi m:norm_bounded_symmetric_form NX NS (phi m).
  exact:(@finite_operator_norm_sform_bounded R m X R^o NX NS hNX hNS (phi m)
    (S*T^+m*(m`!)%:R) (hBound m)).
have hEach m:exists w:Z m,forall u,ev m u w = phi m [tuple u i | i<m].
  exact:(continuous_multilinear_surjective (hZ m) (bounded_sform_finite_family (hPhi m))).
pose w m:=projT1 (cid (hEach m)).
have hW m:=projT2 (cid (hEach m)).
have hNorm m:symmetric_operator_norm hNX.1 NS (phi m) = (N m (w m))%:E.
  apply:(@continuous_multilinear_symmetric_norm R m X R^o (Z m) NX NS hNX hNS
    (ev m) (N m) (hZ m) (w m) (phi m))=>u.
  rewrite hW;congr (phi m _);apply:eq_from_tnth=>i;by rewrite tnth_mktuple ffunE.
pose s:=(Num.bound S).+1.
pose t:=(Num.bound T).+1.
have hSB:S<=s%:R.
  apply:le_trans (ltW (archi_boundP hS)) _;by rewrite /s ler_nat leqnSn.
have hTB:T<=t%:R.
  apply:le_trans (ltW (archi_boundP hT)) _;by rewrite /t ler_nat leqnSn.
have hFormal:@is_formal_analytic_jet R X NX hNX s t w.
  constructor.
  - move=>m sigma u;rewrite !hW;exact:sform_finite_family_symmetric.
  - move=>m.
    have hFirst:=hBound m;rewrite hNorm lee_fin in hFirst.
    apply:le_trans hFirst _.
    apply:ler_wpM2r;first exact:ler0n.
    exact:(ler_pM hS (exprn_ge0 m hT) hSB (lerXn2r m hT (ler0n R t) hTB)).
have [alpha hAlpha]:=@formal_analytic_jet_realisation R X NX hNX a s t w hFormal.
exists alpha=>m u;rewrite hAlpha;exact:hW m u.
Qed.
