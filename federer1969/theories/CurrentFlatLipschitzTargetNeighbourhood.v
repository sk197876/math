(** Federer (1969), 4.1.14, pp. 370–371: a
    target open neighbourhood can be replaced by a larger
    open target without changing the image near its support.
    Use one genuine family valued in the smaller target,
    original smooth composition and weak restriction by
    zero-extended tests. No later support-coincidence theorem
    or nonsmooth pullback action is used. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates LipschitzUP
  OpenLocalLipschitzCompact SmoothCompactSet SmoothCompactNeighbourhoods
  CurrentSpaces CurrentOpenRestriction CurrentNeighbourhoodInclusion
  CurrentCompactInclusionRestriction CurrentCompactMapProper CurrentOpenIdentitySmooth
  CurrentCompactPushforwardAlgebra CurrentCompactPushforwardImages
  CurrentPushforwardDataIndependence SmoothFormPullbackComposition
  FlatCurrentsUP FlatCurrentFinite CurrentLipschitzCompactImage
  CurrentFlatOpenRestriction CurrentCompactLipschitzPushforwardUP
  CurrentFlatLipschitzPushforwardUP CurrentFlatLipschitzPushforwardSealed
  CurrentFlatLipschitzPushforwardBasic CurrentFlatSequenceLimits CurrentWeakSequenceLimit
  CurrentSmoothApproximationUP CurrentCompactSmoothApproximationUP
  CurrentCompactSmoothApproximationSealed CurrentCompactSmoothApproximationOriginal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentSmoothTargetNeighbourhood.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U:set X) (W V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hW:forall y,W y->norm_domain_interior NY W y.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable f:X->Y.
Hypothesis hImageW:forall x,U x->W (f x).
Hypothesis hImageV:forall x,U x->V (f x).
Hypothesis hWV:forall y,W y->V y.
Hypotheses hfW hfV:norm_class_all_orders hNX hNY U f.
Variable T:@current_space R h2 n U hU m.
Hypothesis hCompact:@compact (real_norm_metric_space hNX)
  (@current_support R h2 n U hU m T).
Local Notation Small := (@current_compact_map_pushforward R h2 n nu U W hU hW
  f hImageW hfW m T hCompact).
Local Notation Large := (@current_compact_map_pushforward R h2 n nu U V hU hV
  f hImageV hfV m T hCompact).
Local Notation restriction := (@current_open_restriction R h2 nu m W V hW hV hWV).

(** Source for [current_compact_map_target_neighbourhood_restriction]:
    enlarge the target of an original compact smooth
    image, then restrict it back, by the composition
    and inclusion laws preceding Federer 4.1.14,
    pp. 370–371. Every compact current and arbitrary
    image/smoothness evidence are allowed. *)
Lemma current_compact_map_target_neighbourhood_restriction:
  restriction Large=Small.
Proof.
pose idY:=fun y:Y=>y.
pose hId:=@current_open_identity_smooth R nu W hW.
pose hSmall:=@current_compact_map_image_compact R h2 n nu U W hU hW
  f hImageW hfW m T hCompact.
pose hCompositeImage:=@current_smooth_composite_image R n nu nu U W V
  f idY hImageW hWV.
pose hCompositeClass:=@current_smooth_composite_class R n nu nu U W
  f idY hImageW hfW hId.
have hSame:Large=@current_compact_map_pushforward R h2 n nu U V hU hV
    f hCompositeImage hCompositeClass m T hCompact.
  exact:(@current_pushforward_data_independent R h2 n nu m U V hU hV T f
    hImageV hCompositeImage hfV hCompositeClass _ _).
have hCompose:=@current_compact_map_images_compose R h2 n nu nu U W V
  hU hW hV f idY hImageW hWV hfW hId m T hCompact hSmall.
rewrite hSame hCompose.
exact:(@current_compact_inclusion_restriction R h2 nu W V hW hV hWV
  m Small hSmall hId
  (@current_compact_map_proper R h2 nu nu m W V hW Small idY hWV
    (norm_class_continuous (hId 0%N)) hSmall)).
Qed.
End CurrentSmoothTargetNeighbourhood.

Section CurrentFlatLipschitzTargetNeighbourhood.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U:set X) (W V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hW:forall y,W y->norm_domain_interior NY W y.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable f:X->Y.
Hypothesis hImageW:forall x,U x->W (f x).
Arguments hImageW : clear implicits.
Hypothesis hImageV:forall x,U x->V (f x).
Arguments hImageV : clear implicits.
Hypothesis hWV:forall y,W y->V y.
Arguments hWV : clear implicits.
Hypothesis hLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Variable T:@current_space R h2 n U hU m.
Hypothesis hFlat:@is_flat_current R h2 n m U hU T.
Local Notation QW := (@CurrentFlatLipschitzPushforward.value R h2 n nu m
  U W hU hW f hImageW hLocal T hFlat).
Local Notation QV := (@CurrentFlatLipschitzPushforward.value R h2 n nu m
  U V hU hV f hImageV hLocal T hFlat).
Local Notation restriction := (@current_open_restriction R h2 nu m W V hW hV hWV).

(** Source for [current_flat_lipschitz_target_neighbourhood_restriction]:
    the actual global flat image in V restricts
    to its actual image in W when f(U) lies
    in W contained in V, supporting the original
    composition properties of Federer 4.1.14, p. 371.
    T need not be normal or have finite mass.
    Both target image hypotheses are arbitrary evidence;
    no target convexity or support coincidence is assumed. *)
Theorem current_flat_lipschitz_target_neighbourhood_restriction:
  restriction QV=QW.
Proof.
have[K hK]:=hFlat.
have hQW:=(@CurrentFlatLipschitzPushforward.laws R h2 n nu m
  U W hU hW f hImageW hLocal T hFlat).2 K hK.
have hQV:=(@CurrentFlatLipschitzPushforward.laws R h2 n nu m
  U V hU hV f hImageV hLocal T hFlat).2 K hK.
have hLip:=@norm_open_local_lipschitz_compact R X Y NX NY hNX hNY U f
  (smooth_compact_carrier K) hU hLocal (smooth_compact_is_compact K)
  (smooth_compact_in_domain K).
have[L [hL hBoundK]]:=hLip.
pose hImageK:=fun x (hx:smooth_compact_carrier K x)=>
  hImageW x (smooth_compact_in_domain K x hx).
pose data:=@CurrentCompactSmoothApproximation.value R n nu U W hU hW
  K f L hBoundK hImageK.
pose hApprox:=@CurrentCompactSmoothApproximation.laws R n nu U W hU hW
  K f L hBoundK hImageK.
pose Z:=data.1.
pose g:=data.2.
pose hZ:=current_compact_smooth_domain_open hApprox.
pose hKZ:=current_compact_smooth_domain_contains hApprox.
pose hZU:=@current_compact_smooth_domain_in_domain R n nu U W K f L Z g hApprox.
pose KZ:=@current_compact_index_in_open R n U Z K hKZ.
pose S:=@current_open_restriction R h2 n m Z U hZ hU hZU T.
have hSFlat:=@flat_current_open_restriction R h2 n m U Z hU hZ hZU K hKZ T hK.
pose hCompactS:=@flat_supported_current_compact R h2 n m Z hZ KZ S hSFlat.
have hGW:=@current_compact_smooth_original_approximation R n nu U W K f L Z g hApprox.
have hGV:@is_current_smooth_approximation R n nu Z V KZ f g.
  constructor.
  - move=>i x hx;apply:hWV.
    exact:(@current_smooth_approximation_image R n nu Z W KZ f g hGW i x hx).
  - exact:current_smooth_approximation_class hGW.
  - exact:current_smooth_approximation_bound hGW.
  - exact:current_smooth_approximation_uniform hGW.
pose PW:=fun i=>@current_compact_map_pushforward R h2 n nu Z W hZ hW
  (g i) (current_smooth_approximation_image hGW i)
  (current_smooth_approximation_class hGW i) m S hCompactS.
pose PV:=fun i=>@current_compact_map_pushforward R h2 n nu Z V hZ hV
  (g i) (current_smooth_approximation_image hGV i)
  (current_smooth_approximation_class hGV i) m S hCompactS.
pose fKW:=@current_lipschitz_compact_image R n nu U W hU f hImageW hLocal K.
pose fKV:=@current_lipschitz_compact_image R n nu U V hU f hImageV hLocal K.
have[EW hEW]:=@smooth_compact_neighbourhood_exists R Y NY hNY nu
  (@coordinate_basis R nu) (@coordinate_basisP R nu) W hW fKW.
have[EV hEV]:=@smooth_compact_neighbourhood_exists R Y NY hNY nu
  (@coordinate_basis R nu) (@coordinate_basisP R nu) V hV fKV.
have hInsideW:forall x,smooth_compact_carrier K x->
    norm_domain_interior NY (smooth_compact_carrier EW) (f x).
  move=>x hx;apply:hEW;by exists x.
have hInsideV:forall x,smooth_compact_carrier K x->
    norm_domain_interior NY (smooth_compact_carrier EV) (f x).
  move=>x hx;apply:hEV;by exists x.
have hRecovery:=@flat_current_neighbourhood_inclusion_recovery R h2 n m
  U Z hU hZ hZU K hKZ T hK hCompactS.
have hLimitW:=hQW.2 EW hInsideW Z hZ hZU hKZ S hSFlat hRecovery g hGW.
have hLimitV:=hQV.2 EV hInsideV Z hZ hZU hKZ S hSFlat hRecovery g hGV.
have hWeakW:=@current_flat_sequence_limit_weak R h2 nu m W hW EW PW QW hLimitW.
have hWeakV:=@current_flat_sequence_limit_weak R h2 nu m V hV EV PV QV hLimitV.
have hImages i:restriction (PV i)=PW i.
  exact:(@current_compact_map_target_neighbourhood_restriction R h2 n nu m
    Z W V hZ hW hV (g i)
    (current_smooth_approximation_image hGW i)
    (current_smooth_approximation_image hGV i) hWV
    (current_smooth_approximation_class hGW i)
    (current_smooth_approximation_class hGV i) S hCompactS).
have hWeakRestricted:@is_current_weak_sequence_limit R h2 nu m W hW PW
    (restriction QV).
  move=>phi epsilon hEpsilon.
  have[N hN]:=hWeakV (@current_open_test_extension R h2 nu m W V hW hV hWV phi)
    epsilon hEpsilon.
  exists N=>i hNi.
  rewrite -(hImages i) !current_open_restriction_evaluation.
  exact:hN i hNi.
exact:(@current_weak_sequence_limit_unique R h2 nu m W hW PW
  (restriction QV) QW hWeakRestricted hWeakW).
Qed.

(** Source for [current_flat_lipschitz_target_neighbourhood_compact]:
    the smaller actual image has compact support, by
    its original flat membership in Federer 4.1.14,
    pp. 370–371. Compactness is derived, not an
    additional mathematical hypothesis of inclusion recovery. *)
Lemma current_flat_lipschitz_target_neighbourhood_compact:
  @compact (real_norm_metric_space hNY) (@current_support R h2 nu W hW m QW).
Proof.
have hGlobal:=(@CurrentFlatLipschitzPushforward.laws R h2 n nu m
  U W hU hW f hImageW hLocal T hFlat).1.
have[J hJ]:=hGlobal.
exact:(@flat_supported_current_compact R h2 nu m W hW J QW hJ).
Qed.

(** Source for [current_flat_lipschitz_target_neighbourhood_inclusion]:
    the compact identity inclusion from W to V
    recovers the actual original flat image in V,
    supporting the composition properties of Federer 4.1.14,
    p. 371. Exact image support supplies the
    support-neighbourhood hypothesis. Every compactness witness
    of the smaller actual image is accepted. *)
Theorem current_flat_lipschitz_target_neighbourhood_inclusion
    (hCompact:@compact (real_norm_metric_space hNY)
      (@current_support R h2 nu W hW m QW)):
  @current_compact_map_pushforward R h2 nu nu W V hW hV
    (fun y:Y=>y) hWV (@current_open_identity_smooth R nu W hW) m QW hCompact=QV.
Proof.
have hRestriction:=current_flat_lipschitz_target_neighbourhood_restriction.
have hSupport:@current_support R h2 nu V hV m QV `<=` W.
  move=>y hy.
  have[x hx <-]:=@current_flat_lipschitz_pushforward_support R h2 n nu m U V hU hV
    f hImageV hLocal T hFlat y hy.
  exact:hImageW x hx.1.
pose hId:=@current_open_identity_smooth R nu W hW.
have hCompactR:@compact (real_norm_metric_space hNY)
    (@current_support R h2 nu W hW m (restriction QV)).
  by rewrite hRestriction.
pose hProper:=@current_compact_map_proper R h2 nu nu m W V hW
  (restriction QV) (fun y:Y=>y) hWV (norm_class_continuous (hId 0%N)) hCompactR.
have hRecovery:=@current_neighbourhood_inclusion_recovery R h2 nu m W V hW hV
  hWV hId QV hSupport hProper.
have hSame:=@current_compact_map_pushforward_congruence R h2 nu nu W V hW hV
  (fun y:Y=>y) hWV hId m (restriction QV) QW hCompactR hCompact hRestriction.
exact:(eq_trans (esym hSame) hRecovery).
Qed.
End CurrentFlatLipschitzTargetNeighbourhood.
