(** Federer (1969), 4.1.18, p. 375, first
    proposition: q(xi,eta) belongs to F_(m,K)(U)
    on the literal closed delta tube of the two
    coefficient supports, and F_K(q)<=J(xi,eta).
    Ordinary L1 convolution approximates the two
    pieces by normal currents on that same K. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import CurrentCoefficientNorms Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  CurrentDomain CurrentSpaces CurrentSupportGeometry CurrentMassSealed CurrentBoundary
  CurrentOpenRestriction CurrentOpenRestrictionNormal CurrentOpenRestrictionSupport
  FlatCurrentsUP CurrentFlatNorm NormalCurrentsUP SmoothCompactSet
  CompactSummableMultivectors CompactSummableMultivectorDensity CompactSummableMultivectorSupport
  CompactSummableMultivectorAmbient CompactSummableMultivectorAmbientAgreement
  CompactSummableMultivectorDifference CompactSummableFullConvolutionFamily
  CompactSummableFullConvolutionLone CompactSummableFullConvolutionNormal
  CompactSummableOpenConvolutionMassError CurrentFiniteMassPairFlatApproximation
  CurrentLonePairImageUP CurrentLonePairImageSealed CurrentLonePairCost CurrentLonePairFlatBound
  SmoothingKernelSealed SmoothingDilationSealed SmoothingConvolutionUP
  EuclideanClosedSupportTube EuclideanClosedSupportTubeNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PairFlatMembership.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation FT:=(current_domain R n Full).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation UT:=(current_domain R n U).
Local Notation W d:=(@compact_summable_multivector_space R h2 n d U hU).
Local Notation WF d:=(@compact_summable_multivector_space R h2 n d Full hFull).
Local Notation value d:=(@compact_summable_multivector_value R h2 n d U hU).
Local Notation raw d:=(@compact_summable_multivector_ambient_value R h2 n d U hU).
Local Notation rawF d:=(@compact_summable_multivector_ambient_value R h2 n d Full hFull).
Local Notation sizeF d:=(@compact_summable_multivector_size R h2 n d Full hFull).
Local Notation fieldSupport d:=(@compact_summable_multivector_ambient_support R h2 n d U hU).
Local Notation AF d:=(@compact_summable_multivector_current R h2 n d Full hFull).
Local Notation AU d:=(@compact_summable_multivector_current R h2 n d U hU).
Local Notation restriction d:=(@current_open_restriction R h2 n d U Full hU hFull
  (fun _ _=>Logic.I)).
Local Notation Pairs:=(@current_lone_pair_space R h2 n m U hU).
Local Notation q:=(@CurrentLonePair.map R h2 n m U hU).
Local Notation J:=(@current_lone_pair_cost R h2 n m U hU).
Local Notation phi:=(@SmoothingKernel.value R n).
Local Notation hPhi:=(@SmoothingKernel.laws R n).
Local Notation family:=(@SmoothingDilation.value R n phi).
Local Notation hFamily:=(@SmoothingDilation.laws R n phi).

(** Source for [current_lone_pair_flat_membership]:
    the complete first proposition of Federer
    4.1.18, p. 375. K is exactly the
    displayed closed delta neighbourhood of the two
    literal field supports; the kernel is chosen
    internally from the preceding opaque public laws.
    No finite mass or normality of q is assumed. *)
Theorem current_lone_pair_flat_membership (v:Pairs) delta (hDelta:0<delta)
    (hInside:@euclidean_closed_support_tube R n
      (fieldSupport m v.1 `|` fieldSupport m.+1 v.2) delta `<=` U):
  let L:=fieldSupport m v.1 `|` fieldSupport m.+1 v.2 in
  let K:=@Build_smooth_compact_set R X NX hNX U
    (@euclidean_closed_support_tube R n L delta) hInside
    (@euclidean_closed_support_tube_norm_compact R n L delta
      (compactU
        (@compact_summable_multivector_ambient_support_laws R h2 n m U hU v.1).1
        (@compact_summable_multivector_ambient_support_laws R h2 n m.+1 U hU v.2).1)) in
  @is_flat_current_supported_in R h2 n m U hU K (q v) /\
    (@current_flat_norm R h2 n m U hU K (q v)<=(J v)%:E)%E.
Proof.
move=>L K.
have hXiSupport:fieldSupport m v.1 `<=` smooth_compact_carrier K.
  move=>x hx;apply:(@euclidean_closed_support_tube_includes R n L delta (ltW hDelta)).
  by left.
have hEtaSupport:fieldSupport m.+1 v.2 `<=` smooth_compact_carrier K.
  move=>x hx;apply:(@euclidean_closed_support_tube_includes R n L delta (ltW hDelta)).
  by right.
have hXiOff:forall x:UT,~smooth_compact_carrier K (set_val x)->value m v.1 x=0.
  move=>x hx;rewrite -(compact_summable_multivector_ambient_inside v.1 x).
  apply:((@compact_summable_multivector_ambient_support_laws R h2 n m U hU v.1).2.2).
  move=>h;exact:(hx (hXiSupport (set_val x) h)).
have hEtaOff:forall x:UT,~smooth_compact_carrier K (set_val x)->value m.+1 v.2 x=0.
  move=>x hx;rewrite -(compact_summable_multivector_ambient_inside v.2 x).
  apply:((@compact_summable_multivector_ambient_support_laws R h2 n m.+1 U hU v.2).2.2).
  move=>h;exact:(hx (hEtaSupport (set_val x) h)).
have hASupport:=@compact_summable_multivector_current_support R h2 n m U hU v.1 K hXiOff.
have hBSupport:=@compact_summable_multivector_current_support R h2 n m.+1 U hU v.2 K hEtaOff.
have[xiFull [hXiValue _]]:=@compact_summable_multivector_ambient_representative R h2 n m U hU v.1.
have[etaFull [hEtaValue _]]:=@compact_summable_multivector_ambient_representative R h2 n m.+1 U hU v.2.
have hXiFullSupport:=@compact_summable_multivector_full_support_agreement R h2 n m U hU
  v.1 xiFull hXiValue.
have hEtaFullSupport:=@compact_summable_multivector_full_support_agreement R h2 n m.+1 U hU
  v.2 etaFull hEtaValue.
have[P hP]:=@compact_summable_full_convolution_family_exists R h2 n m
  phi family hPhi hFamily xiFull.
have[Q hQ]:=@compact_summable_full_convolution_family_exists R h2 n m.+1
  phi family hPhi hFamily etaFull.
pose Aeps:=fun epsilon=>restriction m (AF m (P epsilon)).
pose Beps:=fun epsilon=>restriction m.+1 (AF m.+1 (Q epsilon)).
have hNormal:forall epsilon,0<epsilon->epsilon<delta->
    @normal_currents_supported_in R h2 n U hU m K (Aeps epsilon) /\
    @normal_currents_supported_in R h2 n U hU m.+1 K (Beps epsilon).
  move=>epsilon hEpsilon hSmall.
  have[hNormalP hSupportP]:=@compact_summable_full_convolution_normal R h2 n m
    phi family hPhi hFamily epsilon hEpsilon xiFull (P epsilon) (@hP epsilon hEpsilon).1.
  have[hNormalQ hSupportQ]:=@compact_summable_full_convolution_normal R h2 n m.+1
    phi family hPhi hFamily epsilon hEpsilon etaFull (Q epsilon) (@hQ epsilon hEpsilon).1.
  rewrite hXiFullSupport in hSupportP;rewrite hEtaFullSupport in hSupportQ.
  have hPK:@current_support R h2 n Full hFull m (AF m (P epsilon)) `<=`
      smooth_compact_carrier K.
    move=>x hx;apply:(@euclidean_closed_support_tube_mono R n (fieldSupport m v.1)
      L epsilon delta (fun _ h=>or_introl h) (ltW hSmall)).
    exact:(hSupportP x hx).
  have hQK:@current_support R h2 n Full hFull m.+1 (AF m.+1 (Q epsilon)) `<=`
      smooth_compact_carrier K.
    move=>x hx;apply:(@euclidean_closed_support_tube_mono R n (fieldSupport m.+1 v.2)
      L epsilon delta (fun _ h=>or_intror h) (ltW hSmall)).
    exact:(hSupportQ x hx).
  split;split.
  - exact:(@current_normal_neighbourhood_restriction R h2 n U Full hU hFull
      (fun _ _=>Logic.I) m (AF m (P epsilon)) hNormalP
      (subset_trans hPK (smooth_compact_in_domain K))).
  - exact:subset_trans (@current_open_restriction_support_subset R h2 n m
      U Full hU hFull (fun _ _=>Logic.I) (AF m (P epsilon))) hPK.
  - exact:(@current_normal_neighbourhood_restriction R h2 n U Full hU hFull
      (fun _ _=>Logic.I) m.+1 (AF m.+1 (Q epsilon)) hNormalQ
      (subset_trans hQK (smooth_compact_in_domain K))).
  - exact:subset_trans (@current_open_restriction_support_subset R h2 n m.+1
      U Full hU hFull (fun _ _=>Logic.I) (AF m.+1 (Q epsilon))) hQK.
have hLimit:forall tolerance,0<tolerance->exists d:R,0<d /\forall epsilon,0<epsilon->epsilon<d->
    (@CurrentMass.value R h2 n m U hU (AU m v.1-Aeps epsilon)+
      @CurrentMass.value R h2 n m.+1 U hU (AU m.+1 v.2-Beps epsilon)<tolerance%:E)%E.
  move=>tolerance hTolerance.
  have hHalf:0<tolerance/2 by rewrite divr_gt0 // ltr0n.
  have hPConv:forall epsilon,0<epsilon->is_smoothing_convolution
      (@current_vector_mass_real_norm R h2 n m) (family epsilon) (rawF m xiFull) (rawF m (P epsilon)).
    by move=>epsilon hEpsilon;exact:(@hP epsilon hEpsilon).1.
  have hQConv:forall epsilon,0<epsilon->is_smoothing_convolution
      (@current_vector_mass_real_norm R h2 n m.+1) (family epsilon) (rawF m.+1 etaFull) (rawF m.+1 (Q epsilon)).
    by move=>epsilon hEpsilon;exact:(@hQ epsilon hEpsilon).1.
  have[dP [hDP hSmallP]]:=@compact_summable_full_convolution_lone R h2 n m
    phi family hPhi hFamily xiFull P hPConv (tolerance/2) hHalf.
  have[dQ [hDQ hSmallQ]]:=@compact_summable_full_convolution_lone R h2 n m.+1
    phi family hPhi hFamily etaFull Q hQConv (tolerance/2) hHalf.
  exists (Num.min dP dQ);split;first by rewrite lt_min hDP hDQ.
  move=>epsilon hEpsilon hSmall.
  have /andP [hEP hEQ]:(epsilon<dP)&&(epsilon<dQ) by rewrite -lt_min.
  have hPError:=@compact_summable_open_density_mass_error R h2 n m U hU v.1
    xiFull (P epsilon) hXiValue.
  have hQError:=@compact_summable_open_density_mass_error R h2 n m.+1 U hU v.2
    etaFull (Q epsilon) hEtaValue.
  cbn zeta in hPError, hQError.
  rewrite (@compact_summable_multivector_difference_symmetric R h2 n m Full hFull
    xiFull (P epsilon)) in hPError.
  rewrite (@compact_summable_multivector_difference_symmetric R h2 n m.+1 Full hFull
    etaFull (Q epsilon)) in hQError.
  have hBound:=leeD hPError hQError.
  have hStrict:=ltrD (@hSmallP epsilon hEpsilon hEP) (@hSmallQ epsilon hEpsilon hEQ).
  rewrite -splitr in hStrict.
  apply:(le_lt_trans hBound);by rewrite -EFinD lte_fin.
split.
- rewrite CurrentLonePair.laws.
  exact:(@current_finite_mass_pair_flat_approximation R h2 n m U hU K
    (AU m v.1) (AU m.+1 v.2) Aeps Beps delta hASupport hBSupport hDelta hNormal hLimit).
- exact:(@current_lone_pair_flat_bound R h2 n m U hU v K hXiOff hEtaOff).
Qed.
End PairFlatMembership.
