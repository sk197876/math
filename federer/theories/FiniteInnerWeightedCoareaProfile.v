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
  RectifiablePartialCoareaFibres RectifiableWeightedCoareaProfile RectifiableCoareaIntegrands
  FiniteInnerIntegralCoordinates FiniteInnerChartFibres PartialFunctionPrecomposition
  PartialZeroExtension MeasureApproximateJacobian ParameterizedIntegral
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureSubsetIntegral SummableRealFunctionUP
  ExtendedRealOrderTopology HausdorffMeasure MeasureUP MeasureRestriction MeasureBasic
  MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_weighted_coarea_profile]: signed coarea
    in the actual inner spaces of 3.2.48, p. 284. The supporting
    coordinate Jacobian graph is subsequently discharged by the actual
    spherical manifold computation. Whole original fibres remain, even
    on exceptional parameters where the inner signed integral is undefined. *)
Theorem finite_inner_weighted_coarea_profile (R:realType) (V U:lmodType R)
    B C (hB:@is_inner_product R V B) (hC:@is_inner_product R U C)
    N K m q (e:Hom (R_n R N) V) (p:Hom V (R_n R N))
    (a:Hom (R_n R K) U) (t:Hom U (R_n R K))
    (S:set V) (Z:set U) (F:V->U) (w j:V->R):
  is_finite_inner_chart B e p ->is_finite_inner_chart C a t ->
  (q<=m)%N ->
  is_measure_m_rectifiable (@hausdorff_measure R (inner_metric_space hB) m) m S ->
  measure_measurable (@hausdorff_measure R (inner_metric_space hB) m) S ->
  is_measure_m_rectifiable (@hausdorff_measure R (inner_metric_space hC) q) q Z ->
  measure_measurable (@hausdorff_measure R (inner_metric_space hC) q) Z ->
  @is_metric_lipschitz R (inner_metric_space hB) (inner_metric_space hC) S F ->
  (forall x,S x ->Z (F x)) ->
  is_measure_integrable (measure_restrict (@hausdorff_measure R (inner_metric_space hB) m) S)
    (real_total_integrand w) ->
  measure_almost_everywhere_on (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R N)) m) (p @` S)
    [set x|partial_function_graph (measure_approximate_jacobian
      (measure_restrict (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R N)) m) (p @` S))
      m q (partial_function_source_restrict (p @` S)
        (partial_function_total (fun x=>t (F (e x)))))) x (j (e x))] ->
  exists b,is_measure_integral (measure_restrict (@hausdorff_measure R (inner_metric_space hB) m) S)
      (real_total_integrand (fun x=>w x*j x)) b /\
    is_measure_subset_integral (@hausdorff_measure R (inner_metric_space hC) q) Z
      (parameterized_integral (@hausdorff_measure R (inner_metric_space hB) (m-q))
        (fun y=>partial_function_zero_extension (0:extended_real_line R)
          [set x|S x /\F x=y] (real_total_integrand w))) b.
Proof.
move=>hSource hTarget hDim hRS hMS hRZ hMZ hLip0 hRange [b hWeight] hJac.
have [L [_ hL]]:=hLip0.
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
  move=>x y b1 c1 [hx <-] [hy <-].
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
have hWeightC:=(@finite_inner_chart_restricted_integral_coordinates R V B hB N e p m S
  (real_total_integrand w) b hSource).2 hWeight.
have hWeightGraph x z:partial_function_graph (partial_function_precompose e (real_total_integrand w)) x z <->
    partial_function_graph (real_total_integrand (fun x=>w (e x))) x z by [].
have hWC:=measure_integral_graph_equivalent hWeightGraph hWeightC.
have [b0 [hSC hTC]]:=@rectifiable_weighted_coarea_profile R m N q K SC ZC f
  (fun x=>w (e x)) (fun x=>j (e x)) hDim hRSC hMSC hRZC hMZC
  hDomain (ex_intro _ L hLip) hRangeC (ex_intro _ b hWC) hJac.
have hSourceWeight x z:partial_function_graph
    (real_total_integrand (fun x=>w (e x)*j (e x))) x z <->
    partial_function_graph (partial_function_precompose e
      (real_total_integrand (fun x=>w x*j x))) x z by [].
have hOriginalSource:=(@finite_inner_chart_restricted_integral_coordinates R V B hB N e p m S
  (real_total_integrand (fun x=>w x*j x)) b0 hSource).1
  (measure_integral_graph_equivalent hSourceWeight hSC).
pose fibreIntegral:=parameterized_integral (@hausdorff_measure R X (m-q))
  (fun y=>partial_function_zero_extension (0:extended_real_line R)
    [set x|S x /\F x=y] (real_total_integrand w)).
have hFibreGraph y z:
    partial_function_graph (rectifiable_coarea_fibre_integral m q f
      (partial_function_source_restrict SC (real_total_integrand (fun x=>w (e x))))) y z <->
    partial_function_graph fibreIntegral (a y) z.
  rewrite /fibreIntegral /rectifiable_coarea_fibre_integral !parameterized_integral_specification.
  pose g0:=partial_function_zero_extension (0:extended_real_line R)
    [set x|S x /\F x=a y] (real_total_integrand w).
  have hGraph x v0:partial_function_graph
      (partial_function_zero_extension (0:extended_real_line R) (partial_mapping_fibre f y)
        (partial_function_source_restrict SC (real_total_integrand (fun x=>w (e x))))) x v0 <->
      partial_function_graph (partial_function_precompose e g0) x v0.
    have hMember:partial_mapping_fibre f y x <-> S (e x) /\F (e x)=a y.
      split.
      - move=>[hx hF]; split.
        + have [u hu <-]:=hx; by rewrite (finite_inner_chart_right_inverse hSource).
        + have h:=congr1 a hF.
          by rewrite /F0 (finite_inner_chart_right_inverse hTarget) in h.
      - move=>[hx hF]; split.
        + exists (e x); first exact hx.
          exact (finite_inner_chart_left_inverse hSource x).
        + change (t (F (e x))=y); by rewrite hF (finite_inner_chart_left_inverse hTarget).
    match goal with |- ?L <-> _ => change (L <->partial_function_graph g0 (e x) v0) end.
    rewrite /g0 !partial_function_zero_extension_graph.
    split.
    - move=>[[hx [_ hv]]|[hx hv]].
      + left; split; first exact (hMember.1 hx).
        exact hv.
      + right; split; last exact hv.
        by move=>h; apply hx; exact (hMember.2 h).
    - move=>[[hx hv]|[hx hv]].
      + left; split; first exact (hMember.2 hx).
        split; last exact hv.
        exact (hMember.2 hx).1.
      + right; split; last exact hv.
        by move=>h; apply hx; exact (hMember.1 h).
  have hTransport:=@finite_inner_chart_integral_coordinates R V B hB N e p (m-q)%N g0 z hSource.
  split=>hI.
  - apply hTransport.1; exact (measure_integral_graph_equivalent hGraph hI).
  - apply:(measure_integral_graph_equivalent (fun x v0=>iff_sym (hGraph x v0))).
    exact (hTransport.2 hI).
have hOuterGraph y z:partial_function_graph
    (partial_function_zero_extension (0:extended_real_line R) ZC
      (rectifiable_coarea_fibre_integral m q f
        (partial_function_source_restrict SC (real_total_integrand (fun x=>w (e x)))))) y z <->
    partial_function_graph (partial_function_precompose a
      (partial_function_zero_extension (0:extended_real_line R) Z fibreIntegral)) y z.
  match goal with |- ?L <-> _ =>
    change (L <->partial_function_graph (partial_function_zero_extension (0:extended_real_line R) Z fibreIntegral) (a y) z) end.
  have hZC:ZC y <-> Z (a y).
    split.
    - move=>[u hu <-]; by rewrite (finite_inner_chart_right_inverse hTarget).
    - move=>hy; exists (a y); first exact hy.
      exact (finite_inner_chart_left_inverse hTarget y).
  rewrite !partial_function_zero_extension_graph.
  split.
  - move=>[[hy hv]|[hy hv]].
    + left; split; first exact (hZC.1 hy); exact ((hFibreGraph y z).1 hv).
    + right; split; last exact hv.
      by move=>h; apply hy; exact (hZC.2 h).
  - move=>[[hy hv]|[hy hv]].
    + left; split; first exact (hZC.2 hy); exact ((hFibreGraph y z).2 hv).
    + right; split; last exact hv.
      by move=>h; apply hy; exact (hZC.1 h).
exists b0; split; first exact hOriginalSource.
exact ((@finite_inner_chart_integral_coordinates R U C hC K a t q
  (partial_function_zero_extension (0:extended_real_line R) Z fibreIntegral) b0 hTarget).1
  (measure_integral_graph_equivalent hOuterGraph hTC)).
Qed.
