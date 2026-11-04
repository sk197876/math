(** Federer (1969), 3.2.47, p. 283: the reduction
    by 3.2.29 may be performed within the sphere.
    This supporting local argument uses actual manifold coordinates,
    applies 3.2.29 in their parameter space, and maps
    the covering manifolds back through the original inverse. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric
  HilbertFormCompactness NormMetric NormClassOneUP NormRegularity NormClassZeroTopology
  NormCoordinateSystemUP NormCoordinateSubmanifoldImage
  EuclideanSubmanifoldUP SubmanifoldOpenRestriction RectifiableManifoldCoverUP RectifiableClassOneManifoldCover
  InnerClassOneCompactLipschitz MetricLipschitzCompactImage FiniteMeasureRectifiableImages
  LipschitzUP LipschitzBasic RectifiableSetUP HausdorffMeasure HausdorffRestrictedLipschitz
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_coordinate_patch_manifold_cover]:
    the reduction by 3.2.29 in the last paragraph
    of 3.2.47, p. 283, with every covering
    manifold contained in the original containing manifold S.
    Compact cores give both actual coordinate Lipschitz bounds.
    No image measurability or tangent-rank premise is assumed. *)
Theorem rectifiable_coordinate_patch_manifold_cover (R:realType) N d r
    (S T K E:set (R_n R N)) (U:set (R_n R d))
    (phi:R_n R N->R_n R d) (psi:R_n R d->R_n R N):
  is_norm_coordinate_system (inner_norm_real_norm (@euclidean_inner_productP R N))
    (inner_norm_real_norm (@euclidean_inner_productP R d)) S T U phi psi 1%N ->
  @compact (inner_metric_space (@euclidean_inner_productP R N)) K ->
  K `<=` S `&` T ->E `<=` K ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R N)) r) r E ->
  exists C:set (set (R_n R N)),is_countable_submanifold_measure_cover r 1%N E C /\
    (forall M,C M ->M `<=` S).
Proof.
move=>hChart hK hKST hEK hRectE.
pose X:=inner_metric_space (@euclidean_inner_productP R N).
pose Y:=inner_metric_space (@euclidean_inner_productP R d).
pose hX:=@euclidean_inner_productP R N.
pose hY:=@euclidean_inner_productP R d.
pose hNX:=inner_norm_real_norm hX.
pose hNY:=inner_norm_real_norm hY.
have hPhi1:norm_class_one (inner_norm hX) (inner_norm hY) T phi.
  exact ((@norm_class_firstP R (R_n R N) (R_n R d) _ _ hNX hNY T phi).1
    (norm_coordinate_class_forward hChart)).
have hPsi1:norm_class_one (inner_norm hY) (inner_norm hX) U psi.
  exact ((@norm_class_firstP R (R_n R d) (R_n R N) _ _ hNY hNX U psi).1
    (norm_coordinate_class_backward hChart)).
have hPhiLip:=@inner_class_one_compact_lipschitz R (R_n R N) (R_n R d) _ _ hX hY
  T K phi hPhi1 (fun x hx=>(hKST x hx).2) hK.
have [L [hL hBound]]:=hPhiLip.
have hPhiE:@is_metric_lipschitz R X Y E phi.
  exists L; split; first exact hL.
  exact (@metric_lipschitz_bound_restrict R X Y K E phi L hEK hBound).
pose Z:=phi @` E.
have hZRect:is_measure_m_rectifiable (@hausdorff_measure R Y r) r Z.
  exact (hausdorff_measure_rectifiable_lipschitz_image hPhiE hRectE).
have hEST:E `<=` S `&` T.
  move=>x hx; exact (hKST x (hEK x hx)).
have hZU:Z `<=` U.
  move=>z [x hx <-]; exact (norm_coordinate_forward_range hChart (hEST x hx).2).
have [C hC]:=@rectifiable_class_one_manifold_cover R d r Z hZRect.1.
pose G:=fun M:set (R_n R d)=>psi @` (M `&` U).
pose D:=G @` C.
have hDCount:countable D.
  exact (sub_countable (card_image_le _ _) (submanifold_measure_cover_countable hC)).
have hUOpen:@open (real_norm_metric_space hNY) U.
  exact (norm_class_zero_domain_open (norm_class_continuous (norm_coordinate_class_backward hChart))).
have hDMan M (hM:D M):@is_euclidean_submanifold R N r 1%N M.
  have [A hA <-]:=hM.
  have hAMan:=submanifold_measure_cover_class hC hA.
  have hRestricted:=@euclidean_submanifold_open_restriction R d r 1%N A U hAMan hUOpen.
  exact (@euclidean_coordinate_submanifold_image R N d r 1%N S T U (A `&` U) phi psi
    (leqnn 1) hChart hRestricted (fun x hx=>hx.2)).
have hDS M (hM:D M):M `<=` S.
  have [A hA <-]:=hM.
  move=>x [u [_ hu] <-]; exact (norm_coordinate_backward_membership hChart hu).1.
pose P:=phi @` K.
have hPCompact:@compact Y P:=metric_lipschitz_compact_image hK hPhiLip.
have hPU:P `<=` U.
  move=>u [x hx <-]; exact (norm_coordinate_forward_range hChart (hKST x hx).2).
have [L' [_ hPsiBound]]:=@inner_class_one_compact_lipschitz R (R_n R d) (R_n R N) _ _ hY hX
  U P psi hPsi1 hPU hPCompact.
pose A:=Z `\` \bigcup_(M in C) M.
have hAZero:@hausdorff_measure R Y r A=0%E:=submanifold_measure_cover_almost hC.
have hAP:A `<=` P.
  move=>u [hu _]; have [x hx <-]:=hu; exists x; first exact:hEK x hx.
  reflexivity.
have hEstimate:=@hausdorff_lipschitz_on_bound R Y X P psi L' r A hPsiBound hAP.
rewrite hAZero mule0 in hEstimate.
have hPsiAZero:@hausdorff_measure R X r (psi @` A)=0%E.
  apply/eqP; rewrite eq_le hEstimate.
  exact (@measure_nonnegative R X (@hausdorff_measure R X r) (@hausdorff_measure_is_measure R X r) _).
have hRemainder:E `\` \bigcup_(M in D) M `<=` psi @` A.
  move=>x [hx hNot].
  exists (phi x); last exact (norm_coordinate_base_inverse hChart (hEST x hx).1 (hEST x hx).2).
  split; first by exists x.
  move=>[M hM hMx]; apply:hNot.
  exists (G M).
  - by exists M.
  - exists (phi x); first exact (conj hMx (hZU _ ltac:(by exists x))).
    exact (norm_coordinate_base_inverse hChart (hEST x hx).1 (hEST x hx).2).
exists D; split; last exact hDS.
constructor.
- exact hDCount.
- exact hDMan.
- exact (@measure_null_subset R X (@hausdorff_measure R X r) (@hausdorff_measure_is_measure R X r)
    (E `\` \bigcup_(M in D) M) (psi @` A) hRemainder hPsiAZero).
Qed.
