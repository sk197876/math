(** Federer (1969), 4.1.14, p. 372, final sentence:
    choose actual smooth approximants whose differentials converge
    uniformly to the original class-one Df on K. The family is
    specified independently. A compact class-one plateau, its actual
    convolutions and the common-neighbourhood theorem prove existence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormClassOneUP
  NormRegularity GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness SmoothCompactSet SmoothClassOpenRestriction LipschitzUP
  EuclideanOwnNormCompleteness CurrentClassOneCompactPlateau
  NormLocalLipschitzScalarProduct EuclideanLocalLipschitzCompactSupport
  SmoothingKernelSealed SmoothingDilationSealed SmoothingDilationSmooth
  SmoothingDilationNonzeroRadius SmoothingConvolutionUP ContinuousCompactConvolution
  ContinuousSmoothingSmoothness SmoothingLipschitzBound SmoothingLipschitzError
  SmoothLipschitzDifferentialRestriction CurrentMapDifferential CurrentMapDifferentialOpenRestriction
  EuclideanHomOperator GeometricUniformTail AmbientSmoothingCompactNeighbourhood
  ClassOneSmoothingDifferentialUniform CurrentCompactSmoothApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentClassOneSmoothApproximation.
Variable R:realType.
Variables n nu:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation Op:=(@euclidean_operator_norm R n nu).

(** Source for [is_current_class_one_smooth_approximation]: the
    original class-one approximation used for the final evaluation
    formula in Federer 4.1.14, p. 372. Derivative convergence is
    specified explicitly, separately from ordinary value convergence. *)
Record is_current_class_one_smooth_approximation
    (U:set X) (V:set Y) (K:smooth_compact_set hNX U)
    (f:X->Y) (Z:set X) (g:nat->X->Y):Prop:={
  (** Source: the original bounded smooth approximation on one
      neighbourhood, Federer 4.1.14, p. 370. *)
  current_class_one_smooth_ordinary:exists L:R,
    @is_current_compact_smooth_approximation R n nu U V K f L Z g;
  (** Source: actual Dg_i converges to the original Df uniformly on K,
      supporting the class-one clause of Federer 4.1.14, p. 372. *)
  current_class_one_smooth_differential_uniform:forall eta:R,0<eta->exists N:nat,
    forall i:nat,(N<=i)%N->forall x,smooth_compact_carrier K x->
      Op (@current_map_differential R n nu Z (g i) x-
        @current_map_differential R n nu U f x)<eta
}.

Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Arguments hV : clear implicits.
Variable K:smooth_compact_set hNX U.
Variable f:X->Y.
Hypothesis hClass:norm_class_one NX NY U f.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.

(** Source for [current_class_one_smooth_approximation_exists]:
    a smooth family with actual differential convergence for the
    original class-one map, Federer 4.1.14, p. 372. The source
    and target opens are arbitrary; no smooth input, global
    V-valued extension or extra derivative field is assumed. *)
Theorem current_class_one_smooth_approximation_exists:
  exists Z:set X,exists g:nat->X->Y,
    @is_current_class_one_smooth_approximation U V K f Z g.
Proof.
have[F [W [C [hW [hKW [hWU [hAgreement [hC [hCU [hOff [hFClass hDPlateau]]]]]]]]]]]:=
  @current_class_one_compact_plateau_exists R n nu U hU K f hClass.
have hFLocal:=@norm_class_one_locally_metric_lipschitz R X Y NX NY hNX hNY
  (fun _=>True) F hFClass.
have[L [hL hFBound]]:=@euclidean_local_lipschitz_compact_support_global
  R n Y NY hNY F C hC hOff hFLocal.
have[DF hDF]:=hFClass.
have hFContinuous:=norm_class_one_zero hDF.
pose phi:=@SmoothingKernel.value R n.
pose hPhi:=@SmoothingKernel.laws R n.
pose family:=@SmoothingDilation.value R n phi.
pose hFamily:=@SmoothingDilation.laws R n phi.
have hConvolutionExists (e:R):exists ge:X->Y,
    0<e->is_smoothing_convolution hNY (family e) F ge.
  case:(pselect (0<e))=>[he|he].
  - have[ge hConv]:=@continuous_compact_convolution_exists R n Y NY hNY
      (@euclidean_own_norm_complete R nu) F hFContinuous (family e)
      (@smoothing_dilation_smooth R n phi hPhi family hFamily e he) e
      (@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily e he).
    exists ge;by move=>_.
  - exists (fun _=>0);by move=>/he.
have[G hConvolution]:=choice hConvolutionExists.
have hSmooth:forall e:R,0<e->norm_class_all_orders hNX hNY (fun _=>True) (G e).
  move=>e he.
  exact:(@continuous_smooth_convolution_smooth R n Y NY hNY
    (@euclidean_own_norm_complete R nu) F hFContinuous (family e) e (G e)
    (@smoothing_dilation_smooth R n phi hPhi family hFamily e he)
    (@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily e he)
    (hConvolution e he)).
have hAgreementK:forall x,smooth_compact_carrier K x->F x=f x.
  move=>x hx;exact:hAgreement x (hKW x hx).
have hImageK:forall x,smooth_compact_carrier K x->V (f x).
  move=>x hx;exact:hImage x (smooth_compact_in_domain K x hx).
have[r [Z [hr [hZOpen [hContains [hClosureCompact [hClosureInDomain [hEmpty hMaps]]]]]]]]:=
  @ambient_smoothing_compact_neighbourhood R n nu U V hU hV K f F L (ltW hL)
    hFContinuous hFBound hAgreementK hImageK phi hPhi family hFamily G hConvolution.
pose q:R:=1/2.
have hq:0<q<1 by rewrite /q;apply/andP;split;lra.
pose e (i:nat):R:=r*q^+i.
have he:forall i,0<e i by move=>i;exact:mulr_gt0 hr (exprn_gt0 i (andP hq).1).
have heSmall:forall i,e i<=r.
  move=>i;have h:=ler_wpM2l (ltW hr)
    (exprn_ile1 i (ltW (andP hq).1) (ltW (andP hq).2)).
  by rewrite mulr1 in h.
pose g i:=G (e i).
have hGBound:forall i x y,NY (g i x-g i y)<=L*NX (x-y).
  move=>i;exact:(@smoothing_lipschitz_bound R n Y NY hNY phi hPhi family hFamily
    (e i) F (g i) L (he i) (hConvolution (e i) (he i)) hFBound).
have hOrdinary:@is_current_compact_smooth_approximation R n nu U V K f L Z g.
  constructor.
  - exact:ltW hL.
  - exact:hZOpen.
  - exact:hContains.
  - exact:hClosureCompact.
  - exact:hClosureInDomain.
  - exact:hEmpty.
  - move=>i;exact:hMaps (e i) (he i) (heSmall i).
  - move=>i;exact:(@smooth_class_open_restriction R X Y NX NY hNX hNY
      (fun _=>True) Z (g i) (fun _ _=>Logic.I) hZOpen (hSmooth (e i) (he i))).
  - move=>i;split;first exact:ltW hL.
    move=>x y _ _;exact:hGBound i x y.
  - move=>i;exact:(@smooth_global_lipschitz_differential_restriction R n nu
      (g i) L Z (ltW hL) (hSmooth (e i) (he i)) (hGBound i) hZOpen).
  - move=>eta hEta.
    have[N hN]:=@geometric_uniform_tail R q (L*r) eta hq
      (mulr_ge0 (ltW hL) (ltW hr)) hEta.
    exists N=>i hi x hx.
    have hError:=@smoothing_lipschitz_error_bound R n Y NY hNY
      (@euclidean_own_norm_complete R nu) phi hPhi family hFamily (e i) F (g i) L
      (he i) (ltW hL) (hConvolution (e i) (he i)) hFBound x.
    rewrite (hAgreementK x hx) in hError.
    have hReorder:L*e i=q^+i*(L*r) by rewrite /e;ring.
    rewrite hReorder in hError.
    exact:(le_lt_trans hError (hN i hi)).
exists Z,g;constructor;first by exists L.
move=>eta hEta.
pose KWhole:=@Build_smooth_compact_set R X NX hNX (fun _=>True)
  (smooth_compact_carrier K) (fun _ _=>Logic.I) (smooth_compact_is_compact K).
have[d [hd hDerivativeUniform]]:=@class_one_smoothing_differential_uniform R n nu
  phi hPhi family hFamily F G hConvolution hFClass KWhole eta hEta.
have[N hN]:=@geometric_uniform_tail R q r d hq (ltW hr) hd.
exists N=>i hi x hx.
rewrite (@current_map_differential_open_restriction R n nu Z (fun _=>True)
  hZOpen (fun _ _=>Logic.I) (g i) (hSmooth (e i) (he i)) x (hContains x hx)).
rewrite -(hDPlateau x (hKW x hx)).
have hScale:e i<d.
  have h:=hN i hi;by rewrite /e mulrC.
exact:hDerivativeUniform (e i) (he i) hScale x hx.
Qed.
End CurrentClassOneSmoothApproximation.
