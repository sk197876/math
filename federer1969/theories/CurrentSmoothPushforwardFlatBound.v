(** Federer (1969), 4.1.14, p. 371: the original smooth
    images obey the sharp flat bound on the compact source K.
    Apply the attained mass minimum of 4.1.12, pp. 367–368,
    and the two original exterior-power mass estimates. The
    derivative cap is required only on K, and the source
    current need not have finite mass or be normal. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom Bilinear RealNormUP NormMetric
  NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces SmoothCompactSet
  CurrentBoundary CurrentBoundarySupport CurrentSupportGeometry
  CurrentFlatNorm CurrentFlatMinimum CurrentFlatMassComparison CurrentMassSealed
  CurrentMassBasic CurrentCompactMapProper CurrentCompactPushforwardAlgebra
  CurrentPushforwardSealed CurrentPushforwardCongruence CurrentPushforwardSupport
  CurrentPushforwardBoundary CurrentMapDifferential EuclideanHomOperator
  CurrentSmoothPushforwardMassBound CurrentLipschitzFlatCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentSmoothPushforwardFlatBound.
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
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Variable K:smooth_compact_set hNX U.
Variable E:smooth_compact_set hNY V.
Hypothesis hIndex:forall x,smooth_compact_carrier K x->smooth_compact_carrier E (f x).
Variable L:R.
Hypothesis hL:0<=L.
Hypothesis hDerivative:forall x,smooth_compact_carrier K x->
  @euclidean_operator_norm R n nu (@current_map_differential R n nu U f x)<=L.
Local Notation C:=(fun k=>@current_space R h2 n U hU k).
Local Notation D:=(fun k=>@current_space R h2 nu V hV k).
Local Notation support:=(fun k=>@current_support R h2 n U hU k).
Local Notation targetSupport:=(fun k=>@current_support R h2 nu V hV k).
Local Notation compactSupport:=(fun k (T:C k)=>
  @compact (real_norm_metric_space hNX) (support k T)).
Local Notation Push:=(fun k (T:C k) (hT:compactSupport k T)=>
  @current_compact_map_pushforward R h2 n nu U V hU hV f hImage hf k T hT).
Local Notation F:=(fun k=>@current_flat_norm R h2 n k U hU K).
Local Notation G:=(fun k=>@current_flat_norm R h2 nu k V hV E).
Local Notation M:=(fun k=>@CurrentMass.value R h2 n k U hU).
Local Notation N:=(fun k=>@CurrentMass.value R h2 nu k V hV).
Local Notation bd:=(fun k=>@current_boundary R h2 n k U hU).
Local Notation targetBd:=(fun k=>@current_boundary R h2 nu k V hV).

(** Source for [current_smooth_pushforward_supported_image]:
    the original smooth image is supported in any compact E
    containing f(K), supporting the flat estimate in Federer
    4.1.14, p. 371. Reuse the exact support-image law of
    4.1.7, p. 359, with properness only on the actual support. *)
Lemma current_smooth_pushforward_supported_image k (T:C k)
    (hT:compactSupport k T):
  support k T `<=` smooth_compact_carrier K ->
  targetSupport k (Push k T hT) `<=` smooth_compact_carrier E.
Proof.
move=>hSupport y hy.
have[x hx <-]:=@current_pushforward_support_image R h2 n nu k U V hU hV
  T f hImage hf
  (@current_compact_map_proper R h2 n nu k U V hU T f hImage
    (norm_class_continuous (hf 0%N)) hT) y hy.
exact:hIndex x (hSupport x hx).
Qed.

(** Source for [current_smooth_pushforward_flat_bound]: the
    smooth estimate used in Federer's extension from normal
    to flat currents, 4.1.14, p. 371. The displayed source
    flat value alone is assumed finite; the attained decomposition
    supplies the finite masses. The same K-only cap controls both
    degrees and keeps the exact maximum coefficient. *)
Theorem current_smooth_pushforward_flat_bound (T:C m)
    (hT:compactSupport m T):
  support m T `<=` smooth_compact_carrier K ->(F m T < +oo)%E ->
  (G m (Push m T hT)<=
    (current_lipschitz_flat_coefficient m L)%:E*F m T)%E.
Proof.
move=>hSupport hFinite.
have[B [hBSupport [hMinimum hLeast]]]:=
  @current_flat_minimum_attained R h2 n m U hU K T hSupport.
pose A:=T-bd m B.
have hBoundarySupport:support m (bd m B) `<=` smooth_compact_carrier K.
  move=>x hx;exact:hBSupport x
    (@current_boundary_support_subset R h2 n m U hU B x hx).
have hASupport:support m A `<=` smooth_compact_carrier K.
  have h:=@current_support_linear_subset R h2 n m U hU K (-1)
    (bd m B) T hBoundarySupport hSupport.
  by rewrite scaleN1r addrC in h.
have hCost:(M m A+M m.+1 B < +oo)%E.
  by rewrite /A -hMinimum.
have hAFinite:(M m A < +oo)%E.
  exact:le_lt_trans (leeDl (M m A)
    (@current_mass_nonnegative R h2 n m.+1 U hU B)) hCost.
have hBFinite:(M m.+1 B < +oo)%E.
  exact:le_lt_trans (leeDr (M m.+1 B)
    (@current_mass_nonnegative R h2 n m U hU A)) hCost.
pose hA:=@current_support_compact_bound R h2 n m U hU K A hASupport.
pose hB:=@current_support_compact_bound R h2 n m.+1 U hU K B hBSupport.
pose hBoundary:=@current_support_compact_bound R h2 n m U hU K
  (bd m B) hBoundarySupport.
have hBoundaryImage:targetBd m (Push m.+1 B hB)=Push m (bd m B) hBoundary.
  pose hProper:=@current_compact_map_proper R h2 n nu m.+1 U V hU B f
    hImage (norm_class_continuous (hf 0%N)) hB.
  have hCommute:=@current_pushforward_boundary R h2 n nu m U V hU hV
    B f hImage hf hProper.
  apply:(eq_trans hCommute).
  exact:(@current_pushforward_current_congruence R h2 n nu m U V hU hV
    f hImage hf (bd m B) (bd m B) _ _ (erefl _)).
have hResidual:Push m T hT-targetBd m (Push m.+1 B hB)=Push m A hA.
  rewrite hBoundaryImage.
  exact:esym (@current_compact_map_pushforward_subtract R h2 n nu U V hU hV
    f hImage hf m T (bd m B) hT hBoundary hA).
have hMassA:=@current_finite_mass_smooth_pushforward_bound_on_compact
  R h2 n nu m U V hU hV A f hImage hf
  (@current_compact_map_proper R h2 n nu m U V hU A f hImage
    (norm_class_continuous (hf 0%N)) hA) K L hAFinite hL hASupport hDerivative.
have hMassB:=@current_finite_mass_smooth_pushforward_bound_on_compact
  R h2 n nu m.+1 U V hU hV B f hImage hf
  (@current_compact_map_proper R h2 n nu m.+1 U V hU B f hImage
    (norm_class_continuous (hf 0%N)) hB) K L hBFinite hL hBSupport hDerivative.
have hDecomposition:=@current_flat_decomposition_lower_bound R h2 nu m V hV E
  (Push m T hT) (Push m.+1 B hB)
  (current_smooth_pushforward_supported_image hSupport)
  (current_smooth_pushforward_supported_image hBSupport).
rewrite hResidual in hDecomposition.
apply:(le_trans hDecomposition).
apply:(le_trans (leeD hMassA hMassB)).
have[a [ha hAValue]]:=@current_finite_mass_value R h2 n m U hU A hAFinite.
have[b [hb hBValue]]:=@current_finite_mass_value R h2 n m.+1 U hU B hBFinite.
have hFlat:F m T=(a+b)%:E.
  by rewrite hMinimum -/A hAValue hBValue -EFinD.
rewrite hFlat hAValue hBValue -!EFinM -EFinD lee_fin mulrDr.
apply:lerD.
- have hCoef:L^+m<=current_lipschitz_flat_coefficient m L
    by rewrite /current_lipschitz_flat_coefficient le_max lexx.
  exact:(ler_wpM2r ha hCoef).
- have hCoef:L^+m.+1<=current_lipschitz_flat_coefficient m L
    by rewrite /current_lipschitz_flat_coefficient le_max lexx orbT.
  exact:(ler_wpM2r hb hCoef).
Qed.
End CurrentSmoothPushforwardFlatBound.
