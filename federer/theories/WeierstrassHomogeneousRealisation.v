(** Federer (1969), 3.4.6, p. 323: geometric
    bounds on actual homogeneous coefficients produce an analytic
    germ. The proved homogeneous-series realisation supplies existence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals constructive_ereal ring.
From Federer Require Import Hom RealNormUP HomogeneousPolynomialFunctions PolynomialDiagonalNorm PolynomialNorm
  PolynomialPolarizationNorm FactorialExponentialBound SymmetricForms SymmetricOperatorNorm
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousSymmetricFormAdapter ContinuousMultilinearSymmetricNorm
  AnalyticGermUP AnalyticGermJetsSealed FormalAnalyticJetUP FormalAnalyticJetRealisation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_homogeneous_germ_exists]: the
    single-degree grouping of the original double series is
    analytic under its geometric coefficient bound, 3.4.6,
    p. 323. Polarization bounds the actual symmetric
    forms; the proved normal-series theorem then realises their
    jets. Neither convergence nor an analytic sum is assumed. *)
Theorem weierstrass_homogeneous_germ_exists (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (P:nat->X->R) (A B:R):
  0<A ->0<B ->
  (forall m,@is_homogeneous_polynomial R X R^o m (P m)) ->
  (forall m v,NX v<=1 ->`|P m v|<=A*B^+m) ->
  exists alpha:analytic_germ_space hNX (0:X),forall m v,
    P m v=((m`!)%:R)^-1*
      @ContinuousMultilinear.evaluation R m X R^o NX (fun r=>`|r|)
        hNX (@scalar_absolute_value_norm R) [ffun _:'I_m=>v]
        (@AnalyticGermJets.value R X NX hNX 0 m alpha).
Proof.
move=>hA hB hP hBound.
pose F m:=projT1 (cid (hP m)).
have hF m:=projT2 (cid (hP m)).
pose NS:=fun r:R^o=>`|r|.
pose hNS:=@scalar_absolute_value_norm R.
pose Z m:=@ContinuousMultilinear.space R m X R^o NX NS hNX hNS.
pose ev m:=@ContinuousMultilinear.evaluation R m X R^o NX NS hNX hNS.
pose ZN m:=@ContinuousMultilinear.norm R m X R^o NX NS hNX hNS.
pose hZ m:=@ContinuousMultilinear.laws R m X R^o NX NS hNX hNS.
have hNorm m:(symmetric_operator_norm hNX.1 NS (F m)<=
    (A*(4*B)^+m*(m`!)%:R)%:E)%E.
  have hPolynomial:(polynomial_norm hNX.1 NS (sform_polynomial_value (F m))<=
      (A*B^+m)%:E)%E.
    apply:(polynomial_norm_bound hNX.1 NS (sform_polynomial_value (F m)) _).2=>v hv.
    rewrite -(hF m v);exact:hBound m v hv.
  have hPolar:=@polynomial_polarization_finite_norm_bound R X R^o NX NS hNX hNS.1
    m (F m) (A*B^+m) hPolynomial.
  have hExponential:=ler_wpM2r (mulr_ge0 (ltW hA) (exprn_ge0 m (ltW hB)))
    (@factorial_exponential_bound R m).
  have hRight:(4:R)^+m*(m`!)%:R*(A*B^+m)=A*(4*B)^+m*(m`!)%:R.
    by rewrite exprMn;ring.
  rewrite hRight in hExponential.
  exact:le_trans hPolar (lee_tofin hExponential).
pose s:=(Num.bound A).+1.
pose t:=(Num.bound ((4:R)*B)).+1.
have hS:A<=(s%:R:R).
  apply:le_trans (ltW (archi_boundP (ltW hA))) _.
  by rewrite /s ler_nat leqnSn.
have hFour:0<=(4:R)*B:=mulr_ge0 (ler0n R 4) (ltW hB).
have hT:(4:R)*B<=(t%:R:R).
  apply:le_trans (ltW (archi_boundP hFour)) _.
  by rewrite /t ler_nat leqnSn.
have hGrowth m:(symmetric_operator_norm hNX.1 NS (F m)<=
    (s%:R*t%:R^+m*(m`!)%:R)%:E)%E.
  apply:le_trans (hNorm m) _;rewrite lee_fin.
  have hPower:=lerXn2r m hFour (ler0n R t) hT.
  have hProduct:=le_trans (ler_wpM2r (exprn_ge0 m hFour) hS)
    (ler_wpM2l (ler0n R s) hPower).
  have hh:=ler_wpM2r (ler0n R (m`!)) hProduct.
  exact:hh.
have hRepresent m:exists w:Z m,forall u,ev m u w=F m [tuple u i | i<m].
  apply:(@continuous_symmetric_form_representation R m X R^o (Z m) NX NS (ev m) (ZN m) (hZ m) (F m)).
  exact:(@finite_operator_norm_sform_bounded R m X R^o NX NS hNX hNS (F m)
    (s%:R*t%:R^+m*(m`!)%:R) (hGrowth m)).
pose w m:=projT1 (cid (hRepresent m)).
have hEval m:=projT2 (cid (hRepresent m)).
have hFormal:@is_formal_analytic_jet R X NX hNX s t w.
  constructor.
  - move=>m sigma u;rewrite !hEval;exact:sform_finite_family_symmetric.
  - move=>m.
    have hNormEquality:symmetric_operator_norm hNX.1 NS (F m)=(ZN m (w m))%:E.
      apply:(@continuous_multilinear_symmetric_norm R m X R^o (Z m) NX NS hNX hNS (ev m) (ZN m) (hZ m) (w m) (F m))=>u.
      rewrite hEval;congr (F m _);by apply:eq_from_tnth=>i;rewrite tnth_mktuple ffunE.
    have hh:=hGrowth m;by rewrite hNormEquality lee_fin in hh.
have [alpha hAlpha]:=@formal_analytic_jet_realisation R X NX hNX 0 s t w hFormal.
exists alpha=>m v;rewrite hAlpha hEval.
rewrite (hF m v) sform_polynomial_diagonal_value.
change (((m`!)%:R:R)^-1*F m [tuple v | i<m]=
  ((m`!)%:R:R)^-1*F m [tuple [ffun _:'I_m=>v] i | i<m]).
congr (_*F m _);by apply:eq_from_tnth=>i;rewrite !tnth_mktuple ffunE.
Qed.
