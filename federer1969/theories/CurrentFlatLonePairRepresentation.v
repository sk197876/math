(** Federer (1969), 4.1.18, pp. 375–376: the
    original quantitative L1 pair representation on every
    open U. Include the flat current in all of R^n,
    apply the original downward induction there, then
    restrict both compact fields. The original support
    tube and exact cost are unchanged. *)
From mathcomp Require Import all_boot all_order all_algebra
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading EuclideanLebesgueDimensions CurrentDomain CurrentSpaces
  CurrentBoundary CurrentOpenRestriction CurrentOpenRestrictionBoundary
  CurrentLipschitzCompactImage EuclideanFullDomainMeasure
  CurrentFlatNorm FlatCurrentsUP SmoothCompactSet EuclideanClosedSupportTube
  EuclideanClosedSupportTubeNorm CurrentCompactTubeIndex CurrentFlatAmbientInclusion
  CurrentFlatLonePairFullRepresentation CompactSummableMultivectors
  CompactSummableMultivectorDensity CompactSummableMultivectorAmbient
  CompactSummableMultivectorOpenRestriction CurrentLonePairImageUP
  CurrentLonePairImageSealed CurrentLonePairCost
  SmoothingKernelSealed SmoothingDilationSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OriginalOpenRepresentation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation FT:=(current_domain R n Full).
Local Notation WF d:=(@compact_summable_multivector_space R h2 n d Full hFull).
Local Notation valueF d:=(@compact_summable_multivector_value R h2 n d Full hFull).
Local Notation rawF d:=(@compact_summable_multivector_ambient_value R h2 n d Full hFull).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation UT:=(current_domain R n U).
Local Notation P:=(@current_lone_pair_space R h2 n m U hU).
Local Notation q:=(@CurrentLonePair.map R h2 n m U hU).
Local Notation J:=(@current_lone_pair_cost R h2 n m U hU).
Local Notation value d:=(@compact_summable_multivector_value R h2 n d U hU).
Local Notation restriction d:=(@current_open_restriction R h2 n d U Full hU hFull
  (fun _ _=>Logic.I)).

(** Source for [current_flat_lone_pair_representation]: every
    original T in F_(m,K)(U) has q(xi,eta)=T with both
    original coefficient supports inside the literal closed
    delta tube E and J(xi,eta)<=F_K(T)+delta,
    Federer 4.1.18, pp. 375–376. No finite mass,
    normality or integration representation of T is assumed. *)
Theorem current_flat_lone_pair_representation
    (K:smooth_compact_set hNX U)
    (T:@current_space R h2 n U hU m) (delta:R)
    (hFlat:@is_flat_current_supported_in R h2 n m U hU K T)
    (hDelta:0<delta)
    (hInside:@euclidean_closed_support_tube R n (smooth_compact_carrier K) delta `<=` U):
  let E:=@current_compact_closed_tube_index R n U K delta hInside in
  exists v:P,q v=T /\
    (forall x:UT,~smooth_compact_carrier E (set_val x)->value m v.1 x=0) /\
    (forall x:UT,~smooth_compact_carrier E (set_val x)->value m.+1 v.2 x=0) /\
    ((J v)%:E<=@current_flat_norm R h2 n m U hU K T+delta%:E)%E.
Proof.
move=>E.
pose KF:=@current_compact_index_in_open R n U Full K (fun _ _=>Logic.I).
have[Q [hQFlat [hRecovery hNorm]]]:=@current_flat_ambient_inclusion R h2 n m U hU K T hFlat.
pose phi:=@SmoothingKernel.value R n.
pose family:=@SmoothingDilation.value R n phi.
have[vF [hRepresentation [hXiOff [hEtaOff hCost]]]]:=
  @current_flat_lone_pair_full_representation R h2 n phi family
    (@SmoothingKernel.laws R n) (@SmoothingDilation.laws R n phi)
    m KF Q delta hQFlat hDelta.
have hRawOff d (zeta:WF d)
    (hOff:forall x:FT,~smooth_compact_carrier E (set_val x)->valueF d zeta x=0):
    forall x,~smooth_compact_carrier E x->rawF d zeta x=0.
  move=>x hx.
  pose p:=@euclidean_full_domain_point R n x.
  have hValue:=@compact_summable_multivector_ambient_inside R h2 n d Full hFull zeta p.
  change (rawF d zeta x=valueF d zeta p) in hValue.
  rewrite hValue;exact:hOff p hx.
have[xi [hXiValue [hXiRaw [hXiSize [hXiSupport [hXiCarrier hXiCurrent]]]]]]:=
  @compact_summable_multivector_open_restriction R h2 n m U hU vF.1
    (smooth_compact_carrier E) (smooth_compact_is_compact E)
    (smooth_compact_in_domain E) (hRawOff m vF.1 hXiOff).
have[eta [hEtaValue [hEtaRaw [hEtaSize [hEtaSupport [hEtaCarrier hEtaCurrent]]]]]]:=
  @compact_summable_multivector_open_restriction R h2 n m.+1 U hU vF.2
    (smooth_compact_carrier E) (smooth_compact_is_compact E)
    (smooth_compact_in_domain E) (hRawOff m.+1 vF.2 hEtaOff).
have hImage:=congr1 (restriction m) hRepresentation.
rewrite (@CurrentLonePair.laws R h2 n m Full hFull vF)
  (Bilinear.linD (hom_linear (restriction m))) current_open_restriction_boundary
  -hXiCurrent -hEtaCurrent hRecovery in hImage.
have hPair:q (xi,eta)=T.
  rewrite (@CurrentLonePair.laws R h2 n m U hU (xi,eta)) /=.
  exact:hImage.
have hPrice:((J (xi,eta))%:E<=@current_flat_norm R h2 n m U hU K T+delta%:E)%E.
  rewrite /current_lone_pair_cost /= hXiSize hEtaSize.
  by rewrite hNorm in hCost.
exists (xi,eta);split;first exact:hPair.
split;first exact:hXiCarrier.
split;[exact:hEtaCarrier|exact:hPrice].
Qed.
End OriginalOpenRepresentation.
