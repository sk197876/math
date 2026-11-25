(** Federer (1969), 4.1.14, pp. 371–372: smooth the original
    locally Lipschitz map while retaining its continuous Lebesgue-AE
    differential majorant. A compact cutoff preserves f on an open
    plateau. The positive kernel samples only that plateau. Uniform
    continuity of sigma gives a vanishing additive derivative error. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness RealNormUP NormMetric
  NormDifferentialUP NormBoundedLinearTopology NormClassOneUP NormRegularity
  NormClassZeroWhole NormClassZeroTopology NormCompactFunctionBound CompactNearbyUniformContinuity
  SmoothCompactSet SmoothClassOpenRestriction SmoothCompactOpenTubeClosure
  MetricOpenThickening MetricOpenThickeningClosure MetricCompactNeighbourhood
  LipschitzUP EuclideanOwnNormCompleteness CurrentLipschitzCompactPlateau
  EuclideanLocalLipschitzCompactSupport MetricLocalLipschitzContinuity
  SmoothingKernelSealed SmoothingDilationSealed SmoothingDilationSmooth
  SmoothingDilationNonzeroRadius SmoothingConvolutionUP ContinuousCompactConvolution
  ContinuousSmoothingSmoothness SmoothingLipschitzBound SmoothingLipschitzError
  SmoothLipschitzDifferentialRestriction CurrentMapDifferentialOpenRestriction
  GeometricUniformTail EuclideanReflectionTranslation
  CurrentCompactSmoothApproximationUP CurrentCompactMajorantApproximationUP
  CurrentAEMajorantLaws SmoothingAEDifferentialBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCompactMajorantApproximationExistence.
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
Variable sigma:X->R^o.
Hypothesis hLocal:@is_locally_metric_lipschitz R XT YT U f.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hSigma:norm_class_zero NX (fun t:R^o=>`|t|) U sigma.
Hypothesis hMajorant:@is_current_ae_differential_majorant R n nu U f sigma.

(** Source for [current_compact_majorant_smooth_approximation_exists]:
    the smooth approximation preserving the original continuous
    derivative majorant in Federer 4.1.14, pp. 371–372. The only
    original premises are local Lipschitzness, the image in open V,
    continuity of sigma and its actual almost-everywhere Df bound.
    Nonnegativity of sigma is derived. The empty K chooses empty Z. *)
Theorem current_compact_majorant_smooth_approximation_exists:
  exists Z:set X,exists g:nat->X->Y,exists eta:nat->R,
    @is_current_compact_majorant_smooth_approximation R n nu U V K f sigma Z g eta.
Proof.
have hSigmaPositive:=@current_ae_differential_majorant_nonnegative R n nu
  U f sigma hSigma hMajorant.
have[F [W [C [hW [hKW [hWU [hAgreement [hC [hCU [hOff hFLocal]]]]]]]]]]:=
  @current_lipschitz_compact_plateau_exists R X Y NX NY hNX hNY n
    (@coordinate_basis R n) (@coordinate_basisP R n) U hU K f hLocal.
have[L [hL hFBound]]:=@euclidean_local_lipschitz_compact_support_global
  R n Y NY hNY F C hC hOff hFLocal.
have hFContinuous:norm_class_zero NX NY setT F:=
  norm_continuous_whole_class_zero (metric_local_lipschitz_continuous_whole hFLocal).
have hFTopology:continuous (fun x:XT=>(F x:YT)).
  move=>x;exact:(@norm_class_zero_continuous_at R X Y NX NY hNX hNY
    setT F x hFContinuous Logic.I).
have hAgreementK:forall x,smooth_compact_carrier K x->F x=f x.
  move=>x hx;exact:hAgreement x (hKW x hx).
have hImageCompact:@compact YT (F @` smooth_compact_carrier K).
  exact:continuous_compact (continuous_subspaceT hFTopology) (smooth_compact_is_compact K).
have hVOpen:@open YT V.
  rewrite openE=>y hy.
  exact:(@norm_domain_interior_neighbourhood R Y NY hNY V y).1 (hV y hy).
have hImageContained:F @` smooth_compact_carrier K `<=` V.
  move=>y [x hx <-];rewrite (hAgreementK x hx).
  exact:hImage x (smooth_compact_in_domain K x hx).
have[d [hd hTargetTube]]:=@compact_metric_open_thickening R YT
  (F @` smooth_compact_carrier K) V hImageCompact hVOpen hImageContained.
have[w [hw hPlateauTube]]:=@compact_metric_open_thickening R XT
  (smooth_compact_carrier K) W (smooth_compact_is_compact K) hW hKW.
have hWInterior:forall x,W x->norm_domain_interior NX W x.
  move=>x hx.
  exact:(@norm_domain_interior_neighbourhood R X NX hNX W x).2
    (open_nbhs_nbhs (conj hW hx)).
have hFMajorant:=@current_ae_differential_majorant_local_agreement R n nu
  U f sigma W F hWInterior hWU (fun x hx=>esym (hAgreement x hx)) hMajorant.
have[r0 [hr0 hSourceTube]]:=@smooth_compact_open_tube_closure R X NX hNX n
  (@coordinate_basis R n) (@coordinate_basisP R n) U hU K.
pose B:R:=4*(L+1).
have hB:0<B by rewrite /B;nra.
have hdB:0<d/B:=divr_gt0 hd hB.
have hw2:0<w/2 by rewrite divr_gt0 // ltr0n.
pose r:=Num.min (Num.min r0 (d/B)) (w/2).
have hr:0<r by rewrite /r !lt_min hr0 hdB hw2.
have hrMin:r<=Num.min r0 (d/B) by rewrite /r ge_min lexx.
have hrr0:r<=r0.
  have hMin:Num.min r0 (d/B)<=r0 by rewrite ge_min lexx.
  exact:(le_trans hrMin hMin).
have hrTarget:r<=d/B.
  have hMin:Num.min r0 (d/B)<=d/B by rewrite ge_min lexx orbT.
  exact:(le_trans hrMin hMin).
have hrPlateau:r<w.
  have h:r<=w/2 by rewrite /r ge_min lexx orbT.
  lra.
have hProduct:B*r<=d.
  have h:=ler_wpM2l (ltW hB) hrTarget.
  have hCancel:B*(d/B)=d by rewrite mulrC divfK ?gt_eqF.
  by rewrite hCancel in h.
have hMargin:2*L*r<d by rewrite /B in hProduct;nra.
pose Z:set X:=@metric_open_thickening R XT (smooth_compact_carrier K) r.
have hZOpen:forall x,Z x->norm_domain_interior NX Z x.
  move=>x hx.
  exact:(@norm_domain_interior_neighbourhood R X NX hNX Z x).2
    (open_nbhs_nbhs (conj
      (@metric_open_thickening_open R XT (smooth_compact_carrier K) r) hx)).
have hContains:smooth_compact_carrier K `<=` Z:=
  @metric_open_thickening_includes R XT (smooth_compact_carrier K) r hr.
have[hClosureCompact hClosureInDomain]:=hSourceTube r hr hrr0.
pose q:R:=1/2.
have hq:0<q<1 by rewrite /q;apply/andP;split;lra.
pose eta (i:nat):R:=q^+i.
have hEta:forall i,0<eta i.
  move=>i;rewrite /eta;apply:exprn_gt0;exact:(andP hq).1.
have hModulusExists i:exists delta:R,0<delta /\
    forall a y,smooth_compact_carrier K a->U y->NX (y-a)<delta->
      `|sigma y-sigma a|<eta i.
  exact:(@norm_class_zero_compact_uniform_nearby R X R^o NX (fun t:R^o=>`|t|)
    hNX (@scalar_absolute_value_norm R) U (smooth_compact_carrier K) sigma
    (smooth_compact_is_compact K) (smooth_compact_in_domain K) hSigma (eta i) (hEta i)).
have[delta hDelta]:=choice hModulusExists.
pose e (i:nat):R:=Num.min (r*q^+i) (delta i/2).
have he:forall i,0<e i.
  move=>i;rewrite /e lt_min;apply/andP;split.
  - exact:mulr_gt0 hr (exprn_gt0 i (andP hq).1).
  - apply:divr_gt0;first exact:(hDelta i).1.
    by rewrite ltr0n.
have heGeometric:forall i,e i<=r*q^+i by move=>i;rewrite /e ge_min lexx.
have heSmall:forall i,e i<=r.
  move=>i;apply:(le_trans (heGeometric i)).
  have h:=ler_wpM2l (ltW hr)
    (exprn_ile1 i (ltW (andP hq).1) (ltW (andP hq).2)).
  by rewrite mulr1 in h.
have heModulus:forall i,e i<delta i.
  move=>i;have h:e i<=delta i/2 by rewrite /e ge_min lexx orbT.
  have hPositive:0<delta i:=(hDelta i).1;lra.
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
    (e i) F (g i) L (he i) (ltW hL) (hConvolution i) hFBound).
have hOrdinary:@is_current_compact_smooth_approximation R n nu U V K f L Z g.
  constructor.
  - exact:ltW hL.
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
    have hLocalBound:=le_trans (hFBound x a) (ler_wpM2l (ltW hL) hNear).
    have hScale:=ler_wpM2l (ltW hL) (heSmall i).
    have hErrorAt:=hError i x;nra.
  - move=>i;exact:(@smooth_class_open_restriction R X Y NX NY hNX hNY
      setT Z (g i) (fun _ _=>Logic.I) hZOpen (hSmooth i)).
  - move=>i;split;first exact:ltW hL.
    move=>x y _ _;exact:hGBound i x y.
  - move=>i;exact:(@smooth_global_lipschitz_differential_restriction R n nu
      (g i) L Z (ltW hL) (hSmooth i) (hGBound i) hZOpen).
  - move=>eps hEps.
    have hLr:0<=L*r:=mulr_ge0 (ltW hL) (ltW hr).
    have[N hN]:=@geometric_uniform_tail R q (L*r) eps hq hLr hEps.
    exists N=>i hi x hx.
    have hEstimate:=hError i x.
    rewrite (hAgreementK x hx) in hEstimate.
    have hScale:=ler_wpM2l (ltW hL) (heGeometric i).
    have hReorder:L*(r*q^+i)=q^+i*(L*r) by ring.
    rewrite hReorder in hScale.
    exact:(le_lt_trans (le_trans hEstimate hScale) (hN i hi)).
exists Z,g,eta;constructor.
- by exists L.
- exact:hEta.
- move=>eps hEps.
  have[N hN]:=@geometric_uniform_tail R q 1 eps hq ler01 hEps.
  exists N=>i hi;have h:=hN i hi;by rewrite mulr1 in h.
- move=>i a ha.
  rewrite (@current_map_differential_open_restriction R n nu Z setT hZOpen
    (fun _ _=>Logic.I) (g i) (hSmooth i) a (hContains a ha)).
  have hM:0<=sigma a+eta i:=addr_ge0
    (hSigmaPositive a (smooth_compact_in_domain K a ha)) (ltW (hEta i)).
  apply:(@smooth_convolution_ae_differential_bound R n nu F hFLocal
    phi hPhi family hFamily (e i) (he i) (g i) (hConvolution i)
    W sigma hFMajorant a (sigma a+eta i) hM)=>z hNonzero.
  have hRadius:=@smoothing_dilation_nonzero_radius R n phi family hPhi hFamily
    (e i) (he i) z hNonzero.
  have hNear:NX ((a-z)-a)<delta i.
    have hDifference:(a-z)-a = -z by rewrite addrAC subrr add0r.
    rewrite hDifference (real_seminorm_negate hNX.1).
    exact:(lt_trans hRadius (heModulus i)).
  have hPlateau:W (a-z).
    apply:hPlateauTube;exists a;first exact:ha.
    change (is_true (NX (a-(a-z))<w)).
    rewrite (@euclidean_reflection_translation_involutive R n a z).
    exact:(lt_trans (lt_le_trans hRadius (heSmall i)) hrPlateau).
  split;first exact:hPlateau.
  have hOscillation:=(hDelta i).2 a (a-z) ha (hWU (a-z) hPlateau) hNear.
  have hBelow:=ler_norm (sigma (a-z)-sigma a);lra.
Qed.

(** Source for [current_compact_majorant_approximation_data_exists]:
    choose one domain, sequence and error sequence together, supporting
    the original smoothing argument in Federer 4.1.14, pp. 371–372. *)
Theorem current_compact_majorant_approximation_data_exists:
  exists p:(set X)*((nat->X->Y)*(nat->R)),
    @is_current_compact_majorant_smooth_approximation R n nu U V K f sigma p.1 p.2.1 p.2.2.
Proof.
have[Z [g [eta hApproximation]]]:=current_compact_majorant_smooth_approximation_exists.
by exists (Z,(g,eta)).
Qed.
End CurrentCompactMajorantApproximationExistence.
