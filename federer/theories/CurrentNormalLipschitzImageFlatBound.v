(** Federer (1969), 4.1.14, p. 371: the normal-current
    map has flat operator bound max(L^m,L^(m+1)). Reuse
    the attained normal filling of 4.1.12, pp. 367–368,
    the sharp two degree mass bounds and the already
    proved linearity and boundary compatibility. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP SmoothCompactSet CurrentSpaces CurrentBoundary CurrentBoundarySupport
  CurrentSupportGeometry CurrentMassSealed CurrentMassBasic CompactRepresentedCurrentMass
  NormalCurrentsUP NormalCurrentLinear NormalCurrentBoundary FlatCurrentsUP
  FlatCurrentClosure FlatCurrentFinite CurrentFlatNorm CurrentFlatMinimum
  CurrentFlatMassComparison CurrentLipschitzCompactImage CurrentCompactLipschitzPushforwardUP
  CurrentNormalLipschitzImageExistence CurrentNormalLipschitzMassBound
  CurrentCompactLipschitzImageLinear CurrentCompactLipschitzImageBoundary
  CurrentLipschitzFlatCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentNormalLipschitzImageFlatBound.
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
Hypothesis hLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Variable K:smooth_compact_set hNX U.
Local Notation fK:=(@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K).
Local Notation C:=(fun k=>@current_space R h2 n U hU k).
Local Notation D:=(fun k=>@current_space R h2 nu V hV k).
Local Notation F:=(@current_flat_norm R h2 n m U hU K).
Local Notation G:=(@current_flat_norm R h2 nu m V hV fK).
Local Notation M:=(fun k=>@CurrentMass.value R h2 n k U hU).
Local Notation N:=(fun k=>@CurrentMass.value R h2 nu k V hV).
Local Notation bd:=(fun k=>@current_boundary R h2 n k U hU).
Local Notation targetBd:=(fun k=>@current_boundary R h2 nu k V hV).
Local Notation support:=(fun k=>@current_support R h2 n U hU k).
Local Notation Image:=(fun k=>@is_current_compact_lipschitz_image R h2 n nu k
  U V hU hV f hImage hLocal K).

(** Source for [current_normal_lipschitz_image_flat_bound]:
    exactly the compact flat estimate used before bounded
    extension, Federer 4.1.14, p. 371. Any original
    K Lipschitz bound L is permitted; the least constant
    gives the displayed sharp coefficient. Degree zero
    keeps the necessary maximum of 1 and L. *)
Theorem current_normal_lipschitz_image_flat_bound (T:C m) (Q:D m) L:
  @normal_currents_supported_in R h2 n U hU m K T ->Image m T Q ->
  @is_metric_lipschitz_bound R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) (smooth_compact_carrier K) f L ->
  (G Q<=(current_lipschitz_flat_coefficient m L)%:E*F T)%E.
Proof.
move=>hT hQ hLipschitz.
have hTFinite:=@compact_represented_current_finite_mass R h2 n m U hU
  T hT.1.1.1 hT.1.2.
have[B [hNB [hBSupport [hMinimum hLeast]]]]:=
  @current_flat_minimum_normal_filling R h2 n m U hU K T hT.2 hTFinite.
pose A:=T-bd m B.
have hBoundaryNormal:=@normal_current_boundary R h2 n U hU m B hNB.
have hBoundarySupport:support m (bd m B) `<=` smooth_compact_carrier K.
  move=>x hx;exact:hBSupport x
    (@current_boundary_support_subset R h2 n m U hU B x hx).
have hANormal:@is_normal_current R h2 n U hU m A.
  have h:=@normal_current_linear R h2 n U hU m (-1) (bd m B) T hBoundaryNormal hT.1.
  by rewrite scaleN1r addrC in h.
have hASupport:support m A `<=` smooth_compact_carrier K.
  have h:=@current_support_linear_subset R h2 n m U hU K (-1)
    (bd m B) T hBoundarySupport hT.2.
  by rewrite scaleN1r addrC in h.
have[QA [hNQA hQA]]:=@current_normal_lipschitz_image_exists R h2 n nu m U V hU hV
  f hImage hLocal K A hANormal hASupport.
have[QB [hNQB hQB]]:=@current_normal_lipschitz_image_exists R h2 n nu m.+1 U V hU hV
  f hImage hLocal K B hNB hBSupport.
have[QD [hNQD hQD]]:=@current_normal_lipschitz_image_exists R h2 n nu m U V hU hV
  f hImage hLocal K (bd m B) hBoundaryNormal hBoundarySupport.
have hFlatT:=@supported_normal_current_is_flat R h2 n m U hU K T hT.
have hFlatB:=@supported_normal_current_is_flat R h2 n m.+1 U hU K B (conj hNB hBSupport).
have hFlatD:=@supported_normal_current_is_flat R h2 n m U hU K
  (bd m B) (conj hBoundaryNormal hBoundarySupport).
have hBoundaryImage:targetBd m QB=QD.
  exact:(@current_compact_lipschitz_image_boundary R h2 n nu m U V hU hV
    f hImage hLocal K B hFlatB QB QD hQB hQD).
have hACombination:A=(-1:R)*:bd m B+T by rewrite scaleN1r addrC.
have hQACombination:Image m ((-1:R)*:bd m B+T) QA by rewrite -hACombination.
have hImages:=@current_compact_lipschitz_image_linear R h2 n nu m U V hU hV
  f hImage hLocal K (-1) (bd m B) T QD Q QA hFlatD hFlatT hQD hQ hQACombination.
have hResidual:Q-targetBd m QB=QA.
  by rewrite hBoundaryImage hImages scaleN1r addrC.
have hAFinite:=@compact_represented_current_finite_mass R h2 n m U hU
  A hANormal.1.1 hANormal.2.
have hBFinite:=@compact_represented_current_finite_mass R h2 n m.+1 U hU
  B hNB.1.1 hNB.2.
have hFlatA:=@supported_normal_current_is_flat R h2 n m U hU K A (conj hANormal hASupport).
have hMassA:=@current_flat_lipschitz_image_mass_bound R h2 n nu m U V hU hV
  f hImage hLocal K A QA L hFlatA hAFinite hQA hLipschitz.
have hMassB:=@current_flat_lipschitz_image_mass_bound R h2 n nu m.+1 U V hU hV
  f hImage hLocal K B QB L hFlatB hBFinite hQB hLipschitz.
have hDecomposition:=@current_flat_decomposition_lower_bound R h2 nu m V hV fK Q QB
  (@flat_current_supported_support R h2 nu m V hV fK Q hQ.1)
  (@flat_current_supported_support R h2 nu m.+1 V hV fK QB hQB.1).
rewrite hResidual in hDecomposition.
apply:(le_trans hDecomposition);apply:(le_trans (leeD hMassA hMassB)).
have[a [ha hAValue]]:=@current_finite_mass_value R h2 n m U hU A hAFinite.
have[b [hb hBValue]]:=@current_finite_mass_value R h2 n m.+1 U hU B hBFinite.
have hFlat:F T=(a+b)%:E.
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
End CurrentNormalLipschitzImageFlatBound.
