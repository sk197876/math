(** Federer (1969), 3.2.39, pp. 275--276: the
    compact parametrization, finite image layers and mixed radius
    limits give the whole upper bound on the original image. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology ring.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions EuclideanLebesgueBoxes
  LipschitzUP NormMetricScaleContinuity JacobianDensityMeasure EuclideanJacobianFiniteMass
  CompactLipschitzImageMinkowski FiniteCompactJacobianCoverUP FiniteCompactJacobianCover
  RectifiableSetUP RectifiableElementary RectifiableFiniteHausdorffMass RectifiableLowerMinkowskiBound
  HausdorffMeasure HausdorffClosedCoverAgreement BorelRegularMeasureUP
  FiniteFamilyMultiplicity FiniteFamilyLayersUP FiniteFamilyLayerCompactness FiniteFamilyFirstLayer
  FiniteFamilyLayerMeasureSum FiniteMinkowskiLayerTubeSum FiniteExtendedSumWithoutOne
  FiniteRadiusMixedLimitComparison PositiveRadiusLimits PositiveRadiusLimitCongruence
  MinkowskiContents MinkowskiContentsBasic ExtendedScaledErrorBound
  MeasureUP MeasureBasic TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_rectifiable_image_upper_minkowski]:
    the positive-dimensional proof of Federer 3.2.39,
    pp. 275--276, after its compact parametrization. The
    original genuinely rectifiable W is exactly f(A). The
    actual finite compact family has exact Jacobian mass
    and nearly full image cost. Its actual compact image
    layers have the same total Hausdorff mass; the actual
    tube inequality precedes the mixed full-radius limit.
    Only finite Hausdorff and Jacobian scalar values are
    cancelled, with their finiteness derived. No finite
    family, derivative field or content equality is assumed. *)
Theorem compact_rectifiable_image_upper_minkowski (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (A:set (inner_metric_space (@euclidean_inner_productP R m)))
    (W:set (inner_metric_space (@euclidean_inner_productP R n))):
  (0<m<=n)%N ->is_metric_lipschitz setT f ->compact A ->f @` A=W ->
  is_m_rectifiable m W ->
  (upper_minkowski_content m W<=@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m W)%E.
Proof.
move=>/andP[hm0 hmn] hLip hA hImage hW.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose beta:=@hausdorff_measure R Y m.
pose hb:=@hausdorff_measure_is_measure R Y m.
pose nu:=euclidean_jacobian_measure f.
case:(pselect (exists w:Y,W w))=>[[w hw]|hEmpty]; last first.
- have hZero:W=set0.
    apply/seteqP; split=>[y hy|y []]; exfalso; apply:hEmpty; by exists y.
  rewrite hZero (@minkowski_contents_empty R n m).1 (measure_empty hb); exact:lexx.
have hf:continuous (f:X->Y).
  have [L [hL hBound]]:=hLip.
  apply:(@metric_fixed_lipschitz_continuous R X Y f L hBound.1)=>x y.
  exact:hBound.2 x y Logic.I Logic.I.
have hWFinite:beta W \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hb W)); exact:rectifiable_finite_hausdorff_mass hW.
pose p:=fine (beta W).
have hPValue:beta W=p%:E by rewrite /p (fineK hWFinite).
change (upper_minkowski_content m W<=beta W)%E; rewrite hPValue.
apply:(@extended_upper_bound_from_scaled_errors R _ p 1 ler01)=>e he.
rewrite mul1r.
have [I [C hCover]]:=@finite_compact_jacobian_cover_exists R m n f A e hm0 hLip hA he.
have hCCompact (i:I):compact (C i):=
  @jacobian_cover_compact R m n I f A e C hCover i.
have hImageUnion:(\bigcup_i f @` C i)=W.
  by rewrite (finite_compact_jacobian_cover_image_union hCover) hImage.
have [i0 _ hi0]:=(eq_ind W (fun E=>E w) hw _ (esym hImageUnion)).
have hCard:(0<#|I|)%N by apply/card_gt0P; by exists i0.
pose L:=[the finType of 'I_(#|I|)].
pose j0:L:=Ordinal hCard.
have [S hLayers]:=@finite_family_layers_exist Y I (fun i=>f @` C i).
have hFirst:S j0=W.
  rewrite (@finite_family_zero_layer_union Y I (fun i=>f @` C i) S j0 hLayers (erefl _)).
  exact hImageUnion.
have hImageCompact i:compact (f @` C i).
  exact (@continuous_compact [the topologicalType of X] [the topologicalType of Y]
    f (C i) (continuous_subspaceT hf) (hCCompact i)).
have hSCompact j:compact (S j).
  exact:(@finite_family_layers_compact R Y I (fun i=>f @` C i) S hImageCompact hLayers j).
have hWithin j:S j `<=` W.
  rewrite -hImageUnion; exact:(@finite_family_layer_subset_union Y I (fun i=>f @` C i) S hLayers j).
have hSRect j:is_m_rectifiable m (S j):=rectifiable_subset (hWithin j) hW.
have hSFinite j:beta (S j) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hb _)); exact:rectifiable_finite_hausdorff_mass (hSRect j).
have hSValue j:beta (S j)=(fine (beta (S j)))%:E by rewrite (fineK (hSFinite j)).
have hAValueFinite i:nu (C i) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative (euclidean_jacobian_measure_is_measure hLip) _)).
  have hCm:measure_measurable (@euclidean_lebesgue_measure R m) (C i).
    apply:euclidean_borel_measurable; exact:closed_borel_set (compact_closed (@metric_hausdorff R X) (hCCompact i)).
  exact:euclidean_jacobian_finite_source_mass hLip hCm (euclidean_compact_finite (hCCompact i)).
pose a i:=fine (nu (C i)).
have hAValue i:nu (C i)=(a i)%:E by rewrite /a (fineK (hAValueFinite i)).
pose g (j:L) (r:R):= (if j==j0 then 0%E else minkowski_tube_quotient m (S j) r : \bar R).
pose b (j:L):R:=if j==j0 then 0 else fine (beta (S j)).
have hUpper i:(positive_radius_upper_limit (fun r=>minkowski_tube_quotient m (f @` C i) r)<=(a i)%:E)%E.
  change (upper_minkowski_content m (f @` C i)<=(a i)%:E)%E.
  rewrite -hAValue; exact:compact_lipschitz_image_upper_minkowski hmn hLip (hCCompact i).
have hLower j:((b j)%:E<=positive_radius_lower_limit (g j))%E.
  rewrite /b /g; case hEq:(j==j0).
  - by rewrite (@positive_radius_limits_constant R 0%E).2.
  - change ((fine (beta (S j)))%:E<=lower_minkowski_content m (S j))%E.
    rewrite (fineK (hSFinite j)); exact:rectifiable_hausdorff_lower_minkowski_bound hmn (hSRect j).
have hPoint r:0<r ->(minkowski_tube_quotient m W r+(\sum_j g j r)<=
    (\sum_i minkowski_tube_quotient m (f @` C i) r))%E.
  move=>hr; have h:=@finite_minkowski_layer_tube_sum_bound R n m I (fun i=>f @` C i) S r hLayers hr.
  rewrite (@finite_extended_sum_without_one R L j0 (fun j=>minkowski_tube_quotient m (S j) r)) hFirst in h.
  exact h.
have hMixed:=@finite_radius_mixed_limit_comparison R L I
  (fun r=>minkowski_tube_quotient m W r) g
  (fun i r=>minkowski_tube_quotient m (f @` C i) r) a b hUpper hLower hPoint.
change (is_true (upper_minkowski_content m W<=((\sum_i a i)-(\sum_j b j))%R%:E)%E) in hMixed.
have hMeas K:compact K ->measure_measurable beta K.
  move=>hK; exact:(@borel_regular_borel_measurable R Y beta hb (@hausdorff_measure_borel_regular R Y m)
    K (closed_borel_set (compact_closed (@metric_hausdorff R Y) hK))).
have hLayerMass:=@finite_family_layer_measure_sum R Y I beta (fun i=>f @` C i) S
  hb hLayers (fun i=>hMeas _ (hImageCompact i)) (fun j=>hMeas _ (hSCompact j)).
have hMask j:(if j==j0 then 0%E else beta (S j))=(b j)%:E.
  rewrite /b; case:(j==j0); first reflexivity.
  exact:hSValue j.
have hImageMass:(\sum_i beta (f @` C i))%E=(p+(\sum_j b j))%R%:E.
  rewrite -hLayerMass (@finite_extended_sum_without_one R L j0 (fun j=>beta (S j))) hFirst hPValue.
  rewrite (eq_bigr _ (fun j _=>hMask j)) sumEFin -EFinD; reflexivity.
have hASum:(\sum_i a i)%:E=nu A.
  rewrite -sumEFin.
  have hEq:(\sum_i (a i)%:E)%E=(\sum_i nu (C i))%E.
    apply:eq_bigr=>i _; exact:esym (hAValue i).
  exact:eq_trans hEq (jacobian_cover_mass_sum hCover).
have hCost:=jacobian_cover_image_cost hCover.
change (is_true (nu A<=(\sum_i beta (f @` C i))%E+e%:E)%E) in hCost.
rewrite -hASum hImageMass -EFinD lee_fin in hCost.
have hRearrange:(p+e)+(\sum_j b j)=p+(\sum_j b j)+e by ring.
have hFinal:(\sum_i a i)-(\sum_j b j)<=p+e.
  by rewrite lerBlDr hRearrange.
apply:le_trans hMixed _; rewrite lee_fin; exact hFinal.
Qed.
