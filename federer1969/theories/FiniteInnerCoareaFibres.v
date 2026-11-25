(** Federer (1969), 3.2.48, p. 284: the application
    of 3.2.22(2) to the original map between finite inner
    spaces. Public orthonormal chart laws transfer the theorem;
    completed measurable domains and whole original fibres remain. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm InnerMetric FiniteInnerChartUP FiniteInnerChartCompact
  FiniteInnerChartFibres FiniteInnerRectifiableCoordinates
  FiniteInnerChartMeasureTransport FiniteInnerChartMeasuredImages
  FiniteMeasureRectifiableImages LipschitzUP LipschitzBasic
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  PartialMetricLipschitz PartialMappingMultiplicity RectifiableSetUP
  RectifiablePartialCoareaFibres HausdorffMeasure MeasureUP MeasureBasic
  MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_coarea_fibres]: supporting the
    whole-fibre conclusion in 3.2.48, p. 284, by
    3.2.22(2), p. 258. The map is Lipschitz only
    on its original source S. No global Lipschitz extension,
    derivative field, finite individual fibre or Borel-set
    assumption is part of the statement. *)
Theorem finite_inner_coarea_fibres (R:realType) (V U:lmodType R)
    B C (hB:@is_inner_product R V B) (hC:@is_inner_product R U C)
    N K m q (e:Hom (R_n R N) V) (p:Hom V (R_n R N))
    (a:Hom (R_n R K) U) (t:Hom U (R_n R K))
    (S:set V) (Z:set U) (F:V->U):
  is_finite_inner_chart B e p ->is_finite_inner_chart C a t ->
  (q<=m)%N ->
  is_measure_m_rectifiable (@hausdorff_measure R (inner_metric_space hB) m) m S ->
  measure_measurable (@hausdorff_measure R (inner_metric_space hB) m) S ->
  is_measure_m_rectifiable (@hausdorff_measure R (inner_metric_space hC) q) q Z ->
  measure_measurable (@hausdorff_measure R (inner_metric_space hC) q) Z ->
  @is_metric_lipschitz R (inner_metric_space hB) (inner_metric_space hC) S F ->
  (forall x,S x ->Z (F x)) ->
  measure_almost_everywhere_on (@hausdorff_measure R (inner_metric_space hC) q) Z
    [set y|is_measure_m_rectifiable (@hausdorff_measure R (inner_metric_space hB) (m-q))
      (m-q)%N [set x|S x /\F x=y] /\
      measure_measurable (@hausdorff_measure R (inner_metric_space hB) (m-q))
        [set x|S x /\F x=y]].
Proof.
move=>hSource hTarget hDim hRS hMS hRZ hMZ [L [_ hL]] hRange.
pose X:=inner_metric_space hB.
pose Y:=inner_metric_space hC.
pose EC:=inner_metric_space (@euclidean_inner_productP R N).
pose TC:=inner_metric_space (@euclidean_inner_productP R K).
pose SC:=p @` S.
pose ZC:=t @` Z.
pose F0:=fun x:EC=>(t (F (e x)):TC).
pose f:=partial_function_source_restrict SC (partial_function_total F0).
have hRSC:=@finite_inner_chart_measure_rectifiable_coordinates R V B hB N e p m S hSource hRS.
have hMSC:=@finite_inner_chart_coordinates_measurable R V B hB N e p m S hSource hMS.
have hRZC:=@finite_inner_chart_measure_rectifiable_coordinates R U C hC K a t q Z hTarget hRZ.
have hMZC:=@finite_inner_chart_coordinates_measurable R U C hC K a t q Z hTarget hMZ.
have hDomain:partial_function_domain f=SC.
  apply/seteqP; split=>x.
  - by move=>[y [hx _]].
  - move=>hx; exists (F0 x); by split.
have hLip:@is_partial_metric_lipschitz_bound R EC TC f L.
  split; first exact hL.1.
  move=>x y b c [hx <-] [hy <-].
  have hxS:S (e x).
    have [z hz <-]:=hx; by rewrite (finite_inner_chart_right_inverse hSource).
  have hyS:S (e y).
    have [z hz <-]:=hy; by rewrite (finite_inner_chart_right_inverse hSource).
  have hEstimate:=hL.2 (e x) (e y) hxS hyS.
  have hSD:@mdist R X (e x) (e y)=@mdist R EC x y.
    rewrite !inner_metric_distanceE.
    change (inner_norm hB (e x-e y)=inner_norm (@euclidean_inner_productP R N) (x-y)).
    by rewrite -linearB (finite_inner_chart_norm hB hSource).
  have hTD:@mdist R TC (F0 x) (F0 y)=@mdist R Y (F (e x)) (F (e y)).
    rewrite !inner_metric_distanceE /F0.
    change (inner_norm (@euclidean_inner_productP R K) (t (F (e x))-t (F (e y)))=
      inner_norm hC (F (e x)-F (e y))).
    by rewrite -linearB (finite_inner_chart_inverse_norm hC hTarget).
  by rewrite hTD -hSD.
have hRangeC:partial_function_range f `<=` ZC.
  move=>y [x [[z hz <-] <-]]; rewrite /F0 (finite_inner_chart_right_inverse hSource).
  exists (F z); first exact:hRange z hz.
  reflexivity.
have hCore:=@federer_3_2_22_2 R m N q K SC ZC f hDim hRSC hMSC hRZC hMZC
  hDomain (ex_intro _ L hLip) hRangeC.
pose good: set U:=[set y|is_measure_m_rectifiable (@hausdorff_measure R X (m-q)) (m-q)%N
  [set x|S x /\F x=y] /\measure_measurable (@hausdorff_measure R X (m-q)) [set x|S x /\F x=y]].
have hRestore y:
    is_measure_m_rectifiable (@hausdorff_measure R EC (m-q)) (m-q)%N (partial_mapping_fibre f (t y)) /\
    measure_measurable (@hausdorff_measure R EC (m-q)) (partial_mapping_fibre f (t y)) ->good y.
  move=>[hRect hMeas].
  have hFibre:=@finite_inner_chart_fibre_set R V U B C N K e p a t S F y hSource hTarget.
  change (partial_mapping_fibre f (t y)=p @` [set x|S x /\F x=y]) in hFibre.
  have hImage:e @` partial_mapping_fibre f (t y)=[set x|S x /\F x=y].
    rewrite hFibre; exact (@finite_inner_chart_coordinates_image R V B N e p _ hSource).
  split.
  - have hResult:=hausdorff_measure_rectifiable_lipschitz_image
      (@finite_inner_chart_direct_lipschitz R V B hB N e p _ hSource) hRect.
    by rewrite hImage in hResult.
  - have hResult:=@finite_inner_chart_image_measurable R V B hB N e p (m-q)%N _ hSource hMeas.
    by rewrite hImage in hResult.
change (@hausdorff_measure R Y q (Z `\` good)=0)%E.
rewrite -(@finite_inner_chart_inverse_hausdorff R U C hC K a t hTarget q (Z `\` good)).
apply:(@measure_null_subset R TC (@hausdorff_measure R TC q)
  (@hausdorff_measure_is_measure R TC q) _ _ _ hCore).
move=>z [y [hy hBad] <-]; split; first by exists y.
move=>hGood; exact (hBad (hRestore y hGood)).
Qed.
