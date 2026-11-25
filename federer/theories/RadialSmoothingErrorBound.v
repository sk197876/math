(** Federer (1969), 4.1.15, p. 372: the actual two
    convolutions approximate f and g when the independent
    positive parameters r and epsilon are small. The original
    displacement estimate and the earlier smoothing error bound
    give explicit uniform errors, not merely one selected sequence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology ring lra.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  NormRegularity NormClassOneUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct LipschitzUP
  LipschitzBasic EuclideanLipschitzClassZero EuclideanOwnNormCompleteness
  EuclideanHomOperator CurrentMapDifferential SmoothLipschitzDifferentialRestriction
  SmoothingKernelSealed SmoothingDilationSealed SmoothingDilationSmooth
  SmoothingDilationNonzeroRadius ContinuousSmoothingSmoothness
  SmoothingConvolutionUP SmoothingLipschitzBound SmoothingLipschitzError RadialAgreementMapUP
  RadialAgreementMapSealed RadialAgreementMapBounds RadialAgreementMapLipschitz
  MetricOpenThickening RadialAgreementNeighbourhood RadialSmoothingAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RadialSmoothingErrorBound.
Variable R : realType.
Variables n nu : nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation MX := (real_norm_metric_space hNX).
Local Notation MY := (real_norm_metric_space hNY).
Local Notation phi := (@SmoothingKernel.value R n).
Local Notation hPhi := (@SmoothingKernel.laws R n).
Local Notation family := (@SmoothingDilation.value R n phi).
Local Notation hFamily := (@SmoothingDilation.laws R n phi).
Variables F G : X->Y.
Variables Lf Lg : R.
Hypotheses (hLf : 0<=Lf) (hLg : 0<=Lg).
Hypothesis hFBound : forall x y,NY (F x-F y)<=Lf*NX (x-y).
Hypothesis hGBound : forall x y,NY (G x-G y)<=Lg*NX (x-y).

(** Source for [radial_smoothing_simultaneous_error]: the
    first error is at most Lf epsilon and the second at most
    (2Lf+Lg) epsilon+r, supporting the independent-parameter
    approximation in Federer 4.1.15, p. 372. The ambient
    representatives are used only inside this analytic estimate. *)
Theorem radial_smoothing_simultaneous_error r (hr : 0<r)
    epsilon (hEpsilon : 0<epsilon) (a b : X->Y)
    (hA : is_smoothing_convolution hNY (family epsilon) F a)
    (hB : is_smoothing_convolution hNY (family epsilon)
      (@RadialAgreementMap.value R n nu r hr F G) b) :
  forall x,NY (a x-F x)<=Lf*epsilon /\
    NY (b x-G x)<=(2*Lf+Lg)*epsilon+r.
Proof.
pose H:=@RadialAgreementMap.value R n nu r hr F G.
pose hH:=@RadialAgreementMap.laws R n nu r hr F G.
pose C:=2*Lf+Lg.
have hC:0<=C:=addr_ge0 (mulr_ge0 (ler0n R 2) hLf) hLg.
have hFM:@is_metric_lipschitz_bound R MX MY setT F Lf.
  split;first exact:hLf.
  move=>x y _ _;exact:(@hFBound x y).
have hGM:@is_metric_lipschitz_bound R MX MY setT G Lg.
  split;first exact:hLg.
  move=>x y _ _;exact:(@hGBound x y).
have hHBound:forall x y,NY (H x-H y)<=C*NX (x-y).
  move=>x y.
  have hMetric:=@radial_agreement_lipschitz_bound R n nu r hr F G H hH
    setT Lf Lg hFM hGM.
  exact:hMetric.2 x y Logic.I Logic.I.
have hFirst:=@smoothing_lipschitz_error_bound R n Y NY hNY
  (@euclidean_own_norm_complete R nu) phi hPhi family hFamily
  epsilon F a Lf hEpsilon hLf hA hFBound.
have hSecond:=@smoothing_lipschitz_error_bound R n Y NY hNY
  (@euclidean_own_norm_complete R nu) phi hPhi family hFamily
  epsilon H b C hEpsilon hC hB hHBound.
move=>x;split;first exact:(@hFirst x).
have hTriangle:=real_seminorm_triangle hNY.1 (b x-H x) (H x-G x).
have hSplit:(b x-H x)+(H x-G x)=b x-G x by rewrite addrA subrK.
rewrite hSplit in hTriangle.
exact:(le_trans hTriangle (lerD (@hSecond x)
  (@radial_agreement_displacement R n nu r hr F G H hH x))).
Qed.

(** Source for [radial_smoothing_differential_control]: the actual
    differentials of both convolutions have one bound independent
    of the positive r and epsilon, the final smoothing assertion
    of Federer 4.1.15, p. 372. The conclusion is valid
    on every smaller open source, and hence on its original K. *)
Theorem radial_smoothing_differential_control r (hr : 0<r)
    epsilon (hEpsilon : 0<epsilon) (a b : X->Y)
    (hA : is_smoothing_convolution hNY (family epsilon) F a)
    (hB : is_smoothing_convolution hNY (family epsilon)
      (@RadialAgreementMap.value R n nu r hr F G) b) :
  forall (Z : set X)
    (hZ : forall x,Z x->norm_domain_interior NX Z x) x,Z x->
    @euclidean_operator_norm R n nu (@current_map_differential R n nu Z a x)<=Lf /\
    @euclidean_operator_norm R n nu (@current_map_differential R n nu Z b x)<=2*Lf+Lg.
Proof.
pose H:=@RadialAgreementMap.value R n nu r hr F G.
pose hH:=@RadialAgreementMap.laws R n nu r hr F G.
pose C:=2*Lf+Lg.
have hC:0<=C:=addr_ge0 (mulr_ge0 (ler0n R 2) hLf) hLg.
have hFM:@is_metric_lipschitz_bound R MX MY setT F Lf.
  split;first exact:hLf.
  move=>x y _ _;exact:(@hFBound x y).
have hGM:@is_metric_lipschitz_bound R MX MY setT G Lg.
  split;first exact:hLg.
  move=>x y _ _;exact:(@hGBound x y).
have hHBound:forall x y,NY (H x-H y)<=C*NX (x-y).
  move=>x y.
  have hMetric:=@radial_agreement_lipschitz_bound R n nu r hr F G H hH
    setT Lf Lg hFM hGM.
  exact:hMetric.2 x y Logic.I Logic.I.
have hContinuous (P : X->Y) L (hL : 0<=L)
    (hBound : forall x y,NY (P x-P y)<=L*NX (x-y)):
    norm_class_zero NX NY setT P.
  apply:(@euclidean_lipschitz_norm_class_zero R n nu P).
  apply:metric_lipschitz_of_bound;split;first exact:hL.
  move=>x y _ _;change (is_true (NY (P x-P y)<=L*NX (x-y))).
  exact:hBound.
have hKernel:=@smoothing_dilation_smooth R n phi hPhi family hFamily epsilon hEpsilon.
have hOff:=@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily
  epsilon hEpsilon.
have hAClass:=@continuous_smooth_convolution_smooth R n Y NY hNY
  (@euclidean_own_norm_complete R nu) F (@hContinuous F Lf hLf hFBound)
  (family epsilon) epsilon a hKernel hOff hA.
have hBClass:=@continuous_smooth_convolution_smooth R n Y NY hNY
  (@euclidean_own_norm_complete R nu) H (@hContinuous H C hC hHBound)
  (family epsilon) epsilon b hKernel hOff hB.
have hABound:=@smoothing_lipschitz_bound R n Y NY hNY phi hPhi family hFamily
  epsilon F a Lf hEpsilon hA hFBound.
have hBBound:=@smoothing_lipschitz_bound R n Y NY hNY phi hPhi family hFamily
  epsilon H b C hEpsilon hB hHBound.
move=>Z hZ x hx;split.
- exact:(@smooth_global_lipschitz_differential_restriction R n nu a Lf Z
    hLf hAClass hABound hZ x hx).
- exact:(@smooth_global_lipschitz_differential_restriction R n nu b C Z
    hC hBClass hBBound hZ x hx).
Qed.

(** Source for [radial_smoothing_two_parameter_uniform]: both
    actual convolutions approach the original maps uniformly as
    r and epsilon tend independently to zero through positive
    values, the approximation assertion in Federer 4.1.15,
    p. 372. No relation fixing one parameter as a function of
    the other is imposed. *)
Theorem radial_smoothing_two_parameter_uniform delta (hDelta : 0<delta) :
  exists r0 epsilon0 : R,0<r0 /\ 0<epsilon0 /\
    forall r (hr : 0<r) epsilon (hEpsilon : 0<epsilon),
      r<r0->epsilon<epsilon0->forall (a b : X->Y),
      is_smoothing_convolution hNY (family epsilon) F a ->
      is_smoothing_convolution hNY (family epsilon)
        (@RadialAgreementMap.value R n nu r hr F G) b ->
      forall x,NY (a x-F x)<delta /\ NY (b x-G x)<delta.
Proof.
pose C:=2*Lf+Lg.
pose B:=Lf+C+1.
have hC:0<=C:=addr_ge0 (mulr_ge0 (ler0n R 2) hLf) hLg.
have hB:0<B.
  rewrite /B;exact:(ltr_pwDr ltr01 (addr_ge0 hLf hC)).
have hTwo:0<(2:R) by rewrite ltr0n.
have hHalf:0<delta/2:=divr_gt0 hDelta hTwo.
have hRadius:0<delta/(2*B):=divr_gt0 hDelta (mulr_gt0 hTwo hB).
exists (delta/2),(delta/(2*B));split;first exact:hHalf.
split;first exact:hRadius.
move=>r hr epsilon hEpsilon hR hEpsilonSmall a b hA hBConvolution x.
have hErrors:=@radial_smoothing_simultaneous_error r hr epsilon hEpsilon
  a b hA hBConvolution x.
have hWeighted:B*epsilon<delta/2.
  have hMultiply:B*epsilon<B*(delta/(2*B)).
    by rewrite (ltr_pM2l hB).
  have hScale:B*(delta/(2*B))=delta/2.
    field;exact:lt0r_neq0 hB.
  by rewrite hScale in hMultiply.
have hLfB:Lf<=B.
  rewrite /B -addrA lerDl;exact:addr_ge0 hC ler01.
have hCB:C<=B.
  rewrite /B [Lf+C]addrC -addrA lerDl;exact:addr_ge0 hLf ler01.
have hFirst:NY (a x-F x)<delta/2.
  exact:(le_lt_trans (le_trans hErrors.1
    (ler_wpM2r (ltW hEpsilon) hLfB)) hWeighted).
have hSecond:NY (b x-G x)<delta/2+delta/2.
  apply:(le_lt_trans hErrors.2).
  apply:(le_lt_trans (lerD (ler_wpM2r (ltW hEpsilon) hCB) (lexx r))).
  exact:ltrD hWeighted hR.
split.
- apply:(lt_trans hFirst).
  by rewrite ltr_pdivrMr ?ltr0n // ltr_pMr // ltr1n.
- have hSum:delta/2+delta/2=delta by field.
  by rewrite hSum in hSecond.
Qed.

(** Source for [radial_smoothing_fixed_radius_capture]: for every
    fixed r>0 the original coincidence set is contained in
    the displayed agreement locus whenever epsilon is sufficiently
    small, the final proof sentence of Federer 4.1.15,
    p. 372. Ambient Lipschitz representatives are used only
    to quantify the permitted radius uniformly. *)
Theorem radial_smoothing_fixed_radius_capture (A : set X)
    (hAgree : forall x,A x->F x=G x) r (hr : 0<r) :
  exists epsilon0 : R,0<epsilon0 /\
    forall epsilon,0<epsilon->epsilon<epsilon0->
      A `<=` @radial_smoothing_agreement_locus R n nu setT F G r epsilon.
Proof.
pose D:=Lf+Lg.
pose B:=2*(D+1).
have hD:0<=D:=addr_ge0 hLf hLg.
have hD1:0<D+1:=ltr_pwDr ltr01 hD.
have hTwo:(0:R)<2 by rewrite ltr0n.
have hB:0<B.
  rewrite /B;exact:mulr_gt0 hTwo hD1.
pose epsilon0:=r/B.
have hEpsilon0:0<epsilon0:=divr_gt0 hr hB.
have hRadius:B*epsilon0=r by rewrite /epsilon0 mulrC divfK ?gt_eqF.
have hFM:@is_metric_lipschitz_bound R MX MY setT F Lf.
  split;first exact:hLf.
  move=>x y _ _;exact:(@hFBound x y).
have hGM:@is_metric_lipschitz_bound R MX MY setT G Lg.
  split;first exact:hLg.
  move=>x y _ _;exact:(@hGBound x y).
exists epsilon0;split;first exact:hEpsilon0.
move=>epsilon hEpsilon hSmall x hx;split;first exact:Logic.I.
have hWeighted:B*epsilon<r by rewrite -hRadius (ltr_pM2l hB).
have hExpand:B = 2*D+2 by rewrite /B;ring.
have hCoefficient:2*(Lf+Lg)<=B.
  by rewrite hExpand lerDl ler0n.
have hControl:2*(Lf+Lg)*epsilon<r.
  exact:(le_lt_trans (ler_wpM2r (ltW hEpsilon) hCoefficient) hWeighted).
have hTube:@metric_open_thickening R MX A epsilon x.
  exact:(@metric_open_thickening_includes R MX A epsilon hEpsilon x hx).
exact:(@radial_agreement_neighbourhood_ball R n nu F G A Lf Lg hFM hGM
  hAgree r epsilon hEpsilon hControl x hTube).
Qed.
End RadialSmoothingErrorBound.

Arguments radial_smoothing_simultaneous_error : clear implicits.
Arguments radial_smoothing_two_parameter_uniform : clear implicits.
Arguments radial_smoothing_fixed_radius_capture : clear implicits.
