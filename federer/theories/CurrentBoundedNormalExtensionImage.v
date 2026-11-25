(** Federer (1969), 4.1.14, p. 371: the bounded
    extension from normal currents satisfies the full
    original smooth-approximation condition for every
    flat current. Follow the printed three-term error
    split, using normal density and the K-only bound
    for smooth images of the original flat error. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct LipschitzUP OpenLocalLipschitzCompact SmoothCompactSet
  CurrentSpaces CurrentSupportGeometry CurrentOpenRestriction NormalCurrentsUP
  NormalCurrentSpaces FlatCurrentsUP FlatCurrentClosure FlatCurrentFinite FlatCurrentSpaces
  LinearSubspaceRepresentationUP CurrentNormalFlatInclusion
  CurrentLipschitzCompactImage CurrentCompactLipschitzPushforwardUP
  CurrentNormalLipschitzPushforwardUP CurrentLipschitzFlatCoefficient
  CurrentFlatNeighbourhoodRepresentative CurrentFlatOpenRestriction
  CurrentFlatNorm CurrentFlatCompactMonotone CurrentFlatThreeErrorBound
  CurrentSmoothApproximationUP CurrentApproximationOpenRestriction
  CurrentSmoothApproximationFlatDifference CurrentCompactPushforwardAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentBoundedNormalExtensionImage.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Variable K:smooth_compact_set hNX U.
Local Notation fK:=(@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K).
Local Notation A:=(@supported_normal_current_space R h2 n U hU m K).
Local Notation Source:=(@flat_current_space R h2 n m U hU K).
Local Notation Target:=(@flat_current_space R h2 nu m V hV fK).
Local Notation incA:=(@supported_normal_current_inclusion R h2 n U hU m K).
Local Notation incSource:=(@flat_current_inclusion R h2 n m U hU K).
Local Notation incTarget:=(@flat_current_inclusion R h2 nu m V hV fK).
Local Notation SourceNorm:=(@flat_current_norm R h2 n m U hU K).
Local Notation TargetNorm:=(@flat_current_norm R h2 nu m V hV fK).
Local Notation hSourceNorm:=(@flat_current_norm_is_norm R h2 n m U hU K).
Local Notation i:=(@current_normal_flat_inclusion R h2 n m U hU K).
Variable P:Hom A Target.
Hypothesis hP:@is_current_normal_lipschitz_pushforward R h2 n nu m U V hU hV
  f hImage hLocal K P.
Variable G:Hom Source Target.
Variable C:R.
Hypothesis hC:0<=C.
Hypothesis hAgreement:forall a,G (i a) = P a.
Hypothesis hBound:forall z,TargetNorm (G z)<=C*SourceNorm z.

(** Source for [current_bounded_normal_extension_image]: the
    bounded extension retains every original convergence
    requirement, Federer 4.1.14, p. 371. The source
    representative S is arbitrary under its original flat
    membership and inclusion equation. Its normality is
    neither assumed nor needed in the three error terms. *)
Theorem current_bounded_normal_extension_image z:
  @is_current_compact_lipschitz_image R h2 n nu m U V hU hV
    f hImage hLocal K (incSource z) (incTarget (G z)).
Proof.
split;first exact:subspace_representation_member
  (@flat_current_space_laws R h2 nu m V hV fK) (G z).
move=>E hInterior Z hZ hZU hKZ S hS hInclusion g hG.
pose T:=incSource z.
pose Q:=incTarget (G z).
pose KZ:=@current_compact_index_in_open R n U Z K hKZ.
pose restriction:=@current_open_restriction R h2 n m Z U hZ hU hZU.
have hSIdentity:S=restriction T.
  exact:(@current_flat_representative_is_open_restriction R h2 n m U Z
    hU hZ hZU K hKZ T S hS hInclusion).
pose compactS:=@flat_supported_current_compact R h2 n m Z hZ KZ S hS.
have hSupportS:=@flat_current_supported_support R h2 n m Z hZ KZ S hS.
have[c [hc hCap]]:=current_smooth_approximation_bound hG.
pose D:=current_lipschitz_flat_coefficient m c.
have hD:0<=D:=@current_lipschitz_flat_coefficient_nonnegative R m c hc.
have hTargetIndex:smooth_compact_carrier fK `<=` smooth_compact_carrier E.
  move=>y [x hx <-].
  exact:(@norm_domain_interior_member R Y NY hNY (smooth_compact_carrier E)
    (f x) (hInterior x hx)).
move=>epsilon hEpsilon.
pose delta:=epsilon/(2*(C+D+1)).
have hTwo:0<(2:R) by rewrite ltr0n.
have hAtLeast:1<=C+D+1.
  rewrite lerDr;exact:addr_ge0 hC hD.
have hOne:0<C+D+1:=lt_le_trans ltr01 hAtLeast.
have hDen:0<2*(C+D+1):=mulr_gt0 hTwo hOne.
have hDelta:0<delta by rewrite /delta divr_gt0.
have[a hNear]:=@current_normal_flat_inclusion_dense R h2 n m U hU K z delta hDelta.
pose R0:=incA a.
pose QR:=incTarget (P a).
have hRNormal:=subspace_representation_member
  (@supported_normal_current_space_laws R h2 n U hU m K) a.
have hRFlat:=@supported_normal_current_is_flat R h2 n m U hU K R0 hRNormal.
pose AR:=restriction R0.
pose hAR:=@flat_current_open_restriction R h2 n m U Z hU hZ hZU K hKZ R0 hRFlat.
pose compactAR:=@flat_supported_current_compact R h2 n m Z hZ KZ AR hAR.
have hSupportAR:=@flat_current_supported_support R h2 n m Z hZ KZ AR hAR.
have hRecovery:=@flat_current_neighbourhood_inclusion_recovery R h2 n m U Z
  hU hZ hZU K hKZ R0 hRFlat compactAR.
pose push:=fun j X hX=>@current_compact_map_pushforward R h2 n nu Z V hZ hV
  (g j) (current_smooth_approximation_image hG j)
  (current_smooth_approximation_class hG j) m X hX.
have hMiddleLimit:forall eta:R,0<eta->exists N:nat,forall j,(N<=j)%N->
    (@current_flat_norm R h2 nu m V hV E (QR-push j AR compactAR)<eta%:E)%E.
  exact:(hP a).2.2 E hInterior Z hZ hZU hKZ AR hAR hRecovery g hG.
have[N1 hN1]:=hMiddleLimit delta hDelta.
have hSourceValue:@current_flat_norm R h2 n m U hU K (R0-T)=
    (SourceNorm (z-i a))%:E.
  rewrite /R0 /T -(@current_normal_flat_inclusion_value R h2 n m U hU K a)
    -(linB (hom_linear incSource)) flat_current_norm_value.
  by rewrite (real_seminorm_subtract hSourceNorm.1).
have hDifference:AR-S=restriction (R0-T).
  by rewrite hSIdentity (linB (hom_linear restriction)).
have hRestrictedSource:(@current_flat_norm R h2 n m Z hZ KZ (AR-S)<=
    (SourceNorm (z-i a))%:E)%E.
  rewrite hDifference -hSourceValue.
  exact:(@current_open_restriction_flat_norm_le R h2 n m U Z hU hZ hZU K hKZ (R0-T)).
have hFiniteDifference:(@current_flat_norm R h2 n m Z hZ KZ (AR-S) < +oo)%E:=
  le_lt_trans hRestrictedSource (ltry _).
pose hFImage:=fun x (hx:Z x)=>hImage x (hZU x hx).
pose hFLocal:=@metric_local_lipschitz_domain_restriction R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U Z f hZU hLocal.
pose hFContinuous:=@norm_open_local_lipschitz_class_zero R X Y NX NY hNX hNY Z f hZ hFLocal.
have[N2 hN2]:=@current_smooth_approximation_flat_difference_bound R h2 n nu m
  Z V hZ hV KZ f g hG hFImage hFContinuous E hInterior c hc hCap
  AR S compactAR compactS hSupportAR hSupportS hFiniteDifference.
have hFirst:(@current_flat_norm R h2 nu m V hV E (Q-QR)<=(C*delta)%:E)%E.
  apply:(le_trans (@current_flat_compact_monotone R h2 nu m V hV fK E
    hTargetIndex (Q-QR))).
  have hValue:incTarget (G (z-i a))=Q-QR.
    by rewrite (linB (hom_linear G)) hAgreement (linB (hom_linear incTarget)).
  rewrite -hValue flat_current_norm_value lee_fin.
  exact:le_trans (hBound (z-i a)) (ler_wpM2l hC (ltW hNear)).
exists(maxn N1 N2)=>j hNj.
have hj1:=leq_trans (leq_maxl _ _) hNj.
have hj2:=leq_trans (leq_maxr _ _) hNj.
have hSecond:=ltW (hN1 j hj1).
have hThird:(@current_flat_norm R h2 nu m V hV E
    (push j AR compactAR-push j S compactS)<=(D*delta)%:E)%E.
  apply:(le_trans (hN2 j hj2)).
  have hDE:(0<=D%:E)%E by rewrite lee_fin.
  apply:(le_trans (lee_wpmul2l hDE hRestrictedSource)).
  rewrite -EFinM lee_fin.
  change (is_true (D*SourceNorm (z-i a)<=D*delta)).
  exact:(ler_wpM2l hD (ltW hNear)).
have hTotal:=@current_flat_three_error_bound R h2 nu m V hV E
  Q QR (push j AR compactAR) (push j S compactS)
  (C*delta) delta (D*delta) hFirst hSecond hThird.
apply:(le_lt_trans hTotal);rewrite lte_fin.
have hEnd:delta*(2*(C+D+1))=epsilon by rewrite /delta divfK ?gt_eqF.
have hHalf:C*delta+delta+D*delta=epsilon/2 by nra.
rewrite hHalf;lra.
Qed.
End CurrentBoundedNormalExtensionImage.
