(** Federer (1969), 4.1.14, p. 370: construct one smooth
    approximating family near K by 4.1.2, pp. 346–347. Recalling
    2.10.43, p. 201, first extend f restricted to K with its original
    sharp Lipschitz bound. The extension takes values in ambient
    Euclidean space; a uniform tube keeps the smoothed maps in V. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  NormClassOneUP NormRegularity NormClassZeroTopology SmoothClassOpenRestriction
  SmoothCompactSet SmoothCompactOpenTubeClosure MetricOpenThickening
  MetricOpenThickeningClosure MetricCompactNeighbourhood LipschitzUP LipschitzBasic
  KirszbraunExtensionUP KirszbraunExtension EuclideanLipschitzClassZero
  EuclideanOwnNormCompleteness SmoothingKernelSealed SmoothingDilationSealed
  SmoothingDilationSmooth SmoothingDilationNonzeroRadius SmoothingConvolutionUP
  ContinuousCompactConvolution ContinuousSmoothingSmoothness SmoothingLipschitzBound
  SmoothingLipschitzError GeometricUniformTail SmoothLipschitzDifferentialRestriction
  CurrentCompactSmoothApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCompactSmoothApproximationExistence.
Variable R:realType.
Variables n nu:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation YT:=(real_norm_metric_space hNY).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Arguments hV : clear implicits.
Variable K:smooth_compact_set hNX U.
Variable f:X->Y.
Variable L:R.
Hypothesis hBoundK:@is_metric_lipschitz_bound R XT YT (smooth_compact_carrier K) f L.
Hypothesis hImageK:forall x,smooth_compact_carrier K x->V (f x).
Arguments hImageK : clear implicits.

(** Source for [current_compact_smooth_approximation_exists]: existence
    of a smooth approximating sequence in Federer 4.1.14, p. 370,
    with the exact compact-restriction bound supplied by 2.10.43.
    The original open V may be disconnected or empty. The empty K
    produces the empty Z without choosing any element of V. *)
Theorem current_compact_smooth_approximation_exists:
  exists Z:set X,exists g:nat->X->Y,
    @is_current_compact_smooth_approximation R n nu U V K f L Z g.
Proof.
have hL:0<=L:=hBoundK.1.
have hInnerBound:@is_metric_lipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R nu))
    (smooth_compact_carrier K) f L.
  split;first exact:hL.
  move=>x y hx hy.
  change (is_true (NY (f x-f y)<=L*NX (x-y))).
  exact:hBoundK.2 x y hx hy.
pose F:=@euclidean_lipschitz_extension R n nu (smooth_compact_carrier K) f L hInnerBound.
have hF:=@euclidean_lipschitz_extension_specification R n nu
  (smooth_compact_carrier K) f L hInnerBound.
have hAgreement:forall x,smooth_compact_carrier K x->F x=f x.
  exact:kirszbraun_extension_agreement_law hF.
have hFullBound:=kirszbraun_extension_bound_law hF.
have hFBound:forall x y,NY (F x-F y)<=L*NX (x-y).
  move=>x y;exact:hFullBound.2 x y Logic.I Logic.I.
have hFContinuous:norm_class_zero NX NY setT F.
  apply:(@euclidean_lipschitz_norm_class_zero R n nu F).
  exact:metric_lipschitz_of_bound hFullBound.
have hFTopology:continuous (fun x:XT=>(F x:YT)).
  move=>x;exact:(@norm_class_zero_continuous_at R X Y NX NY hNX hNY
    setT F x hFContinuous Logic.I).
have hImageCompact:@compact YT (F @` smooth_compact_carrier K).
  exact:continuous_compact (continuous_subspaceT hFTopology) (smooth_compact_is_compact K).
have hVOpen:@open YT V.
  rewrite openE=>y hy.
  exact:(@norm_domain_interior_neighbourhood R Y NY hNY V y).1 (hV y hy).
have hImageContained:F @` smooth_compact_carrier K `<=` V.
  move=>y [x hx <-];rewrite (hAgreement x hx);exact:hImageK x hx.
have[d [hd hTargetTube]]:=@compact_metric_open_thickening R YT
  (F @` smooth_compact_carrier K) V hImageCompact hVOpen hImageContained.
have[r0 [hr0 hSourceTube]]:=@smooth_compact_open_tube_closure R X NX hNX n
  (@coordinate_basis R n) (@coordinate_basisP R n) U hU K.
pose B:R:=4*(L+1).
have hB:0<B by rewrite /B;nra.
pose r:=Num.min r0 (d/B).
have hr:0<r by rewrite /r lt_min hr0 divr_gt0.
have hrr0:r<=r0 by rewrite /r ge_min lexx.
have hrTarget:r<=d/B by rewrite /r ge_min lexx orbT.
have hProduct:B*r<=d.
  have h:=ler_wpM2l (ltW hB) hrTarget.
  have hCancel:B*(d/B)=d by rewrite mulrC divfK ?gt_eqF.
  by rewrite hCancel in h.
have hMargin:2*L*r<d by rewrite /B in hProduct;nra.
pose Z:set X:=@metric_open_thickening R XT (smooth_compact_carrier K) r.
have hZOpen:forall x,Z x->norm_domain_interior NX Z x.
  have hOpen:@open XT Z:=@metric_open_thickening_open R XT (smooth_compact_carrier K) r.
  rewrite openE in hOpen.
  move=>x hx;exact:(@norm_domain_interior_neighbourhood R X NX hNX Z x).2 (hOpen x hx).
have hContains:smooth_compact_carrier K `<=` Z:=
  @metric_open_thickening_includes R XT (smooth_compact_carrier K) r hr.
have[hClosureCompact hClosureInDomain]:=hSourceTube r hr hrr0.
pose q:R:=1/2.
have hq:0<q<1 by rewrite /q;apply/andP;split;lra.
pose e (i:nat):R:=r*q^+i.
have he:forall i,0<e i.
  move=>i;exact:mulr_gt0 hr (exprn_gt0 i (andP hq).1).
have heSmall:forall i,e i<=r.
  move=>i;have h:=ler_wpM2l (ltW hr)
    (exprn_ile1 i (ltW (andP hq).1) (ltW (andP hq).2)).
  by rewrite mulr1 in h.
pose phi:=@SmoothingKernel.value R n.
pose hPhi:=@SmoothingKernel.laws R n.
pose family:=@SmoothingDilation.value R n phi.
pose hFamily:=@SmoothingDilation.laws R n phi.
have hConvolutionExists i:exists gi:X->Y,is_smoothing_convolution hNY (family (e i)) F gi.
  exact:(@continuous_compact_convolution_exists R n Y NY hNY
    (@euclidean_own_norm_complete R nu) F hFContinuous (family (e i))
    (@smoothing_dilation_smooth R n phi hPhi family hFamily (e i) (he i)) (e i)
    (@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily (e i) (he i))).
have[g hConvolution]:=choice hConvolutionExists.
have hSmooth:forall i,norm_class_all_orders hNX hNY setT (g i).
  move=>i.
  exact:(@continuous_smooth_convolution_smooth R n Y NY hNY
    (@euclidean_own_norm_complete R nu) F hFContinuous (family (e i)) (e i) (g i)
    (@smoothing_dilation_smooth R n phi hPhi family hFamily (e i) (he i))
    (@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily (e i) (he i))
    (hConvolution i)).
have hGBound:forall i x y,NY (g i x-g i y)<=L*NX (x-y).
  move=>i;exact:(@smoothing_lipschitz_bound R n Y NY hNY phi hPhi family hFamily
    (e i) F (g i) L (he i) (hConvolution i) hFBound).
have hError:forall i x,NY (g i x-F x)<=L*e i.
  move=>i;exact:(@smoothing_lipschitz_error_bound R n Y NY hNY
    (@euclidean_own_norm_complete R nu) phi hPhi family hFamily
    (e i) F (g i) L (he i) hL (hConvolution i) hFBound).
exists Z,g;constructor.
- exact:hL.
- exact:hZOpen.
- exact:hContains.
- exact:hClosureCompact.
- exact:hClosureInDomain.
- move=>hEmpty;rewrite /Z hEmpty;exact:(@metric_open_thickening_empty R XT r).
- move=>i x [a ha hax];apply:hTargetTube.
  exists (F a);first by exists a.
  change (is_true (NY (F a-g i x)<d)).
  rewrite (real_seminorm_subtract hNY.1).
  have hNear:NX (x-a)<=r.
    change (is_true (NX (a-x)<r)) in hax.
    rewrite (real_seminorm_subtract hNX.1);exact:ltW hax.
  have hTriangle:=real_seminorm_triangle hNY.1 (g i x-F x) (F x-F a).
  have hSplit:(g i x-F x)+(F x-F a)=g i x-F a by rewrite addrA subrK.
  rewrite hSplit in hTriangle.
  have hLocal:=le_trans (hFBound x a) (ler_wpM2l hL hNear).
  have hScale:=ler_wpM2l hL (heSmall i).
  have hErrorAt:=hError i x.
  nra.
- move=>i;exact:(@smooth_class_open_restriction R X Y NX NY hNX hNY
    setT Z (g i) (fun _ _=>Logic.I) hZOpen (hSmooth i)).
- move=>i;split;first exact:hL.
  move=>x y _ _;exact:hGBound i x y.
- move=>i;exact:(@smooth_global_lipschitz_differential_restriction R n nu
    (g i) L Z hL (hSmooth i) (hGBound i) hZOpen).
- move=>eta hEta.
  have hLr:0<=L*r:=mulr_ge0 hL (ltW hr).
  have[N hN]:=@geometric_uniform_tail R q (L*r) eta hq hLr hEta.
  exists N=>i hi x hx.
  have hEstimate:=hError i x.
  rewrite (hAgreement x hx) in hEstimate.
  have hReorder:L*e i=q^+i*(L*r) by rewrite /e;ring.
  rewrite hReorder in hEstimate.
  exact:(le_lt_trans hEstimate (hN i hi)).
Qed.

(** Source for [current_compact_smooth_approximation_data_exists]:
    choose the domain and the sequence as one witness of the original
    smoothing existence assertion, Federer 4.1.14, p. 370. This prepares
    the opaque family without choosing unrelated witnesses separately. *)
Theorem current_compact_smooth_approximation_data_exists:
  exists p:(set X)*(nat->X->Y),
    @is_current_compact_smooth_approximation R n nu U V K f L p.1 p.2.
Proof.
have[Z [g hg]]:=current_compact_smooth_approximation_exists.
by exists (Z,g).
Qed.
End CurrentCompactSmoothApproximationExistence.
