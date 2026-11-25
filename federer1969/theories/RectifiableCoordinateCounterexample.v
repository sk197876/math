(** Federer (1969), 3.2.27, pp. 262–263: local
    counterexample to the upper bound without source
    measurability. This example is not printed in the
    working erratum. A nonmeasurable subset of the unit
    interval and its complement occupy two parallel
    segments. Both actual coordinate counting integrals
    exist, but their sum is smaller than outer length. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  RealMetricBackground RealMetricCompleteness RealLineSeparability LebesgueScalarMeasure
  EuclideanOneCoordinate EuclideanCoordinateMetric EuclideanLebesgueBoxes
  CoordinateProjection SingleCoordinateProjection TwoCoordinateSelections ParallelCoordinateSheets
  TwoSheetProjectionIntegrals FiniteSplitMeasurability BernsteinNonmeasurableSubset
  RectifiableSetUP RectifiableElementary RectifiableUnion RectifiableFiniteHausdorffMass
  RectifiableCoordinateMassUP RectifiableCoordinateCounterexampleUP RectifiableCoordinateProjectionBounds ExteriorIndices
  HausdorffMeasure MeasureUP MeasureBasic BorelRegularMeasureUP
  ExtendedRealOrderTopology MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_coordinate_upper_requires_measurability]:
    local correction of the upper inequality in 3.2.27,
    pp. 262–263, using 2.2.4, p. 62, and
    3.2.14, pp. 251–252. The source is genuinely
    one-rectifiable and has finite Hausdorff mass. Its
    two actual projection integrals are one and zero;
    its outer length is strictly greater than one.
    The source is therefore not Hausdorff measurable,
    as also follows from the corrected theorem. *)
Theorem rectifiable_coordinate_upper_requires_measurability (R:realType):
  exists (W:set (R_n R 2)) (a:Lambda 2 1->R),
    is_rectifiable_coordinate_counterexample W a.
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R 2).
pose H:=@hausdorff_measure R X 1.
pose Y:=real_line_metric R.
pose mu:=@lebesgue_scalar_measure R.
pose A:set Y:=`[(0%R:R),1%R].
have hMu:=@lebesgue_scalar_is_measure R.
have hAMeas:measure_measurable mu A:=@lebesgue_scalar_segment_measurable R 0%R 1%R.
have hMassA:mu A= 1 by rewrite /mu /A lebesgue_scalar_segment // subr0.
have hPositive:0<mu A by rewrite hMassA lte_fin ltr01.
have hFinite:mu A < +oo by rewrite hMassA ltry.
have [V [hVA hNot]]:=@borel_regular_nonmeasurable_subset R Y mu hMu
  (@lebesgue_scalar_borel_regular R) A (@real_line_metric_complete R)
  (@real_line_countable_dense R) hPositive hFinite (fun t _=>lebesgue_scalar_singleton t).
pose L0:=@euclidean_coordinate_line R 2 ord0 (0%R:X).
pose L1:=@euclidean_coordinate_line R 2 ord0 (@coordinate_basis R 2 ord_max).
pose W:=(L0 @` V) `|` (L1 @` (A `\` V)).
pose lambda0:=single_coordinate_selection (ord0:'I_2).
pose lambda1:=single_coordinate_selection (ord_max:'I_2).
pose F0:=@coordinate_projection R 2 1 lambda0.
pose F1:=@coordinate_projection R 2 1 lambda1.
pose a (lambda:Lambda 2 1):R:=if lambda==lambda0 then 1%R else 0%R.
have hDistinct:lambda0!=lambda1:=two_coordinate_selections_distinct.
have hCoordinates (h:R) (t:Y):
    F0 (@euclidean_coordinate_line R 2 ord0 (h*:@coordinate_basis R 2 ord_max)%R t)=euclidean_one_embed t /\
    F1 (@euclidean_coordinate_line R 2 ord0 (h*:@coordinate_basis R 2 ord_max)%R t)=euclidean_one_embed h.
  split; apply/ffunP=>k.
  - rewrite /F0 /lambda0 single_coordinate_projection_value
      (@parallel_coordinate_line_first R h t).
    by rewrite /euclidean_one_embed ffunE.
  - rewrite /F1 /lambda1 single_coordinate_projection_value
      (@parallel_coordinate_line_second R h t).
    by rewrite /euclidean_one_embed ffunE.
have h00 t:F0 (L0 t)=euclidean_one_embed t.
  have h:=(hCoordinates 0%R t).1; by rewrite scale0r in h.
have h01 t:F0 (L1 t)=euclidean_one_embed t.
  have h:=(hCoordinates 1%R t).1; by rewrite scale1r in h.
have h10 t:F1 (L0 t)=euclidean_one_embed 0%R.
  have h:=(hCoordinates 0%R t).2; by rewrite scale0r in h.
have h11 t:F1 (L1 t)=euclidean_one_embed 1%R.
  have h:=(hCoordinates 1%R t).2; by rewrite scale1r in h.
have hHorizontal:=@two_sheet_horizontal_unit_integral R (Choice.clone X _) L0 L1 F0 V hVA h00 h01.
have hVertical:=@two_sheet_vertical_integral_zero R (Choice.clone X _) L0 L1 F1 A V h10 h11.
have hMasses:is_rectifiable_coordinate_masses W a.
  move=>lambda; have [h0|h1]:=two_coordinate_selections lambda.
  - rewrite h0 /a eqxx; exact hHorizontal.
  - rewrite h1 /a eq_sym (negbTE hDistinct); exact hVertical.
have hSum:(\sum_lambda a lambda)%R= 1%R.
  rewrite (bigD1 lambda0) //= /a eqxx.
  have hOther:(\sum_(lambda:Lambda 2 1 | lambda!=lambda0)
      (if lambda==lambda0 then (1%R:R) else 0%R))%R = 0%R.
    apply:big1=>lambda hn; by rewrite (negbTE hn).
  by rewrite hOther addr0.
have hE0:@is_m_rectifiable R X 1 (L0 @` A).
  have h:=@parallel_coordinate_segment_rectifiable R 0%R; by rewrite scale0r in h.
have hE1:@is_m_rectifiable R X 1 (L1 @` A).
  have h:=@parallel_coordinate_segment_rectifiable R 1%R; by rewrite scale1r in h.
have hSub:W `<=` (L0 @` A) `|` (L1 @` A).
  move=>x [[t ht hTx]|[t [ht hn] hTx]].
  - left; exists t; first exact:hVA t ht; exact hTx.
  - right; by exists t.
have hRect:@is_m_rectifiable R X 1 W:=rectifiable_subset hSub (rectifiable_union hE0 hE1).
have hMeasureRect:=rectifiable_hausdorff_measure_rectifiable hRect.
have hMass:H W=mu V+mu (A `\` V).
  exact:(@parallel_coordinate_sheets_union_mass R V (A `\` V) hVA).
have hRegular:=@borel_regular_is_regular R [the topologicalType of Y] mu hMu
  (@lebesgue_scalar_borel_regular R).
have hStrict:=@regular_nonmeasurable_split_strict R (Choice.clone Y _) mu A V
  hMu hRegular hAMeas hFinite hVA hNot.
rewrite hMassA in hStrict.
have hExcess:(\sum_lambda a lambda)%R%:E<H W by rewrite hSum hMass.
have hNonmeas:~measure_measurable H W.
  move=>hW.
  have [_ hUpper]:=@federer_3_2_27 R 1 2 (erefl true) W a hMeasureRect hW hMasses.
  have hBad:=lt_le_trans hExcess hUpper; by rewrite ltxx in hBad.
exists W,a; constructor.
- exact hRect.
- exact hMeasureRect.
- exact hMasses.
- split; first by rewrite /a eqxx.
  by rewrite /a eq_sym (negbTE hDistinct).
- exact hSum.
- by rewrite -hSum.
- exact hNonmeas.
Qed.
