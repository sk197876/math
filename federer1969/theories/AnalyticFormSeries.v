(** Federer (1969), 3.4.5, p. 319: analytic
    realisation of bounded symmetric coefficient sequences.
    The proof uses the actual homogeneous series and
    termwise differentiation of 3.1.24, pp. 238–239. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology constructive_ereal lra ring.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP NormDifferentialUP NormRegularity NormClassOneUP NormClassZeroTopology
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm ContinuousMultilinearZero
  NormHigherDifferentialUP NormHigherDifferentialUnique NormClassInfinityPolynomial
  NormAffineDilationDifferentials NormOpenDomainLaws NormLinearDomainLaws
  SymmetricForms SymmetricOperatorNorm HomogeneousPolynomialFunctions PolynomialTaylorTerms ContinuousSymmetricFormAdapter
  ShiftedHomogeneousDifferentials AnalyticCoefficientMajorant NormAnalyticUP NormPolynomialSeriesAnalytic
  NormGeometricSeriesUniform NormalSeriesDerivativeLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bounded_analytic_form_series_exists]: the
    analytic realisation implicit in coefficient compactness,
    3.4.5, p. 319. Actual bounded symmetric forms
    with an analytic factorial bound give an analytic function
    and all of its actual derivative-series limits on a
    genuine positive-radius neighbourhood. No function or
    derivative realisation is supplied as an extra premise. *)
Theorem bounded_analytic_form_series_exists (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (hComplete:is_complete_metric_space (real_norm_metric_space hNY))
    (phi:forall m,S_m X Y m) (a:X) (c:R):
  0<c ->(forall m,norm_bounded_symmetric_form NX NY (phi m)) ->
  (forall m,(1<=m)%N ->
    (symmetric_operator_norm hNX.1 NY (phi m)<=(c^+m*(m`!)%:R)%:E)%E) ->
  exists r:R,0<r /\exists f:X->Y,
    @norm_analytic_at R X Y NX NY hNX hNY setT f a /\
    exists E:forall m:nat,forall i,X->@ContinuousMultilinear.space R i X Y NX NY hNX hNY,
    exists G:forall i,X->@ContinuousMultilinear.space R i X Y NX NY hNX hNY,
      (forall m i x u,@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY u (E m i x)=
        symmetric_taylor_term i (phi m) (x-a) [tuple u j | j<i]) /\
      (forall i x,NX (x-a)<r ->has_norm_higher_differential NX
        (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY)
        (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY)
        (fun y=>NX (y-a)<r) f i x (G i x)) /\
      forall i x,NX (x-a)<r ->
        ((fun N=>((\sum_(m<N) E m i x):real_norm_metric_space
          (continuous_multilinear_norm_is_norm hNY (@ContinuousMultilinear.laws R i X Y NX NY hNX hNY)))) @ \oo -->
          (G i x:real_norm_metric_space
            (continuous_multilinear_norm_is_norm hNY (@ContinuousMultilinear.laws R i X Y NX NY hNX hNY)))).
Proof.
move=>hc hPhiBound hPhiNorm.
pose Z i:=@ContinuousMultilinear.space R i X Y NX NY hNX hNY.
pose ev i:=@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY.
pose ZN i:=@ContinuousMultilinear.norm R i X Y NX NY hNX hNY.
have hZ i:is_continuous_multilinear_space NX NY (ev i) (ZN i).
  exact:ContinuousMultilinear.laws.
have hex m:=@shifted_homogeneous_differential_fields R X Y NX NY hNX hNY Z ev ZN hZ
  m (phi m) a (hPhiBound m).
pose E m:=projT1 (cid (hex m)).
have hE m:=projT2 (cid (hex m)).
pose Q m x:=sform_polynomial_value (phi m) (x-a).
pose r:=(1/(4*c))%R.
pose q:=(1/2:R).
pose W:=fun x=>NX (x-a)<r.
have hcNonnegative:0<=c:=ltW hc.
have hcNe:c!=0:=lt0r_neq0 hc.
have hr:0<r by rewrite /r divr_gt0 // mulr_gt0 // ltr0n.
have hq:0<q<1 by rewrite /q;apply/andP;split;lra.
have hEquation:q= 2*c*r by rewrite /q /r;field;exact:hcNe.
have ha:W a by rewrite /W subrr (real_seminorm_zero hNX.1).
have hOpen x (hx:W x):norm_domain_interior NX W x.
  exact:(@norm_open_ball_domain_interior R X NX hNX a r x hx).
have hQ m:norm_class_zero NX NY setT (Q m).
  have hRaw:=@norm_class_infinity_sform_polynomial R X Y NX NY hNX hNY Z ev ZN hZ setT
    (fun x _=>norm_full_domain_interior NX x) m (phi m) (hPhiBound m).
  have hShift:=@norm_class_infinity_affine_dilation R X Y NX NY hNX hNY Z ev ZN hZ
    (sform_polynomial_value (phi m)) 1 (-a) hRaw.
  have hFunction:(fun x=>sform_polynomial_value (phi m) (1*:x-a))=Q m.
    by apply:funext=>x;rewrite /Q scale1r.
  rewrite hFunction in hShift;exact:(hShift 0%N).1.
have hEval m i x u:@ev i u (E m i x)=symmetric_taylor_term i (phi m) (x-a) [tuple u j | j<i].
  exact:((hE m).1 i x u).
have hActual m i x:has_norm_higher_differential NX ev ZN setT (Q m) i x (E m i x).
  exact:((hE m).2.1 i x).
have hContinuous m i:norm_class_zero NX (@ZN i) setT (E m i).
  exact:((hE m).2.2 i).
have hZero x:@ev 0%N [ffun j:'I_0=>(0:X)] (E 0%N 0%N x)=Q 0%N x.
  exact:(hActual 0%N 0%N x).2.
have [M [hM [hMPositive hMajorant]]]:=@analytic_coefficient_geometric_majorants R X Y NX NY hNX hNY
  Z ev ZN hZ phi E W a c r q hcNonnegative (ltW hr) hq hEquation
  (fun x hx=>ltW hx) hPhiNorm hEval hZero.
pose F N x:=\sum_(m<N) Q m x.
have hIncrement N x (hx:W x):NY (F N.+1 x-F N x)<=q^+N*M 0%N.
  rewrite /F big_ord_recr /= addrAC subrr add0r.
  have hBound:=hMajorant 0%N N x hx.
  rewrite (continuous_multilinear_zero_norm hNY (hZ 0%N)) (hActual N 0%N x).2 in hBound.
  exact:hBound.
have [f [hPointwise [hError hUniform]]]:=@norm_geometric_series_uniform_limit R X Y NY hNY hComplete
  W F q (M 0%N) hq (hM 0%N) hIncrement.
have hAnalytic:@norm_analytic_at R X Y NX NY hNX hNY setT f a.
  apply:(@norm_polynomial_series_analytic R X Y NX NY hNX hNY hComplete setT f a).
  exists W;split;first exact:hOpen a ha.
  split;first by move=>x hx.
  exists (fun m=>sform_polynomial_value (phi m));split.
  - move=>m;split;first by exists (phi m).
    have hRaw:=@norm_class_infinity_sform_polynomial R X Y NX NY hNX hNY Z ev ZN hZ setT
      (fun x _=>norm_full_domain_interior NX x) m (phi m) (hPhiBound m).
    move=>x;exact:(@norm_class_zero_continuous_at R X Y NX NY hNX hNY setT
      (sform_polynomial_value (phi m)) x (hRaw 0%N).1 Logic.I).
  - move=>epsilon hEpsilon;have [k hk]:=hUniform epsilon hEpsilon.
    exists k=>N hN x hx.
    have hKN:(k<=N.+1)%N:=leq_trans hN (leqnSn N).
    have hh:=hk N.+1 hKN x hx.
    rewrite (real_seminorm_subtract hNY.1) in hh;exact:hh.
have [G [hClass [hActualG [hNormG hLimits]]]]:=@norm_geometric_smooth_series_with_limits
  R X Y NX NY hNX hNY hComplete Z ev ZN hZ W Q E f q M
  (@norm_open_ball_convex R X NX hNX a r) hOpen hq hM hQ hActual hContinuous hMajorant hUniform.
exists r;split;first exact:hr.
exists f;split;first exact:hAnalytic.
exists E,G;split;first exact:hEval.
split;first exact:hActualG.
exact:hLimits.
Qed.
