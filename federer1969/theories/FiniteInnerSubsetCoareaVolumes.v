(** Federer (1969), 3.2.28(2),(3), pp. 265–266:
    coarea on finite rectifiable Borel subsets of actual inner-product manifolds,
    through orthonormal Euclidean ambient coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric
  FiniteInnerChartUP FiniteInnerChartCompact EuclideanSubmanifoldUP NormDifferentialUP TangentConeUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialMetricLipschitz
  PartialMappingMultiplicity PartialExteriorNormUP LipschitzUP MeasureUP HausdorffMeasure
  RectifiableCoarea RectifiableCoareaConstantVolumes SubmanifoldSubsetTangentJacobian FiniteInnerRectifiableCoordinates RectifiableSetUP HausdorffClosedCoverAgreement
  BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_inner_subset_coarea_volumes]:
    the constant-Jacobian coarea step of 3.2.47(3),
    p. 283, by 3.2.22(3), pp. 258–260.
    Source and target need only be finite rectifiable
    Borel sets; the source lies in a class-one
    manifold of the same dimension. Actual differential,
    tangent norm and fibre mass premises are explicit. *)
Theorem finite_inner_subset_coarea_volumes (R:realType)
    (V U:lmodType R) (B:V->V->R) (C:U->U->R)
    (hB:is_inner_product B) (hC:is_inner_product C) N K d q
    (e:Hom (R_n R N) V) (p:Hom V (R_n R N))
    (a:Hom (R_n R K) U) (t:Hom U (R_n R K))
    (M S:set V) (T:set U) (F:V->U) (j:R) (lambda : \bar R):
  is_finite_inner_chart B e p ->is_finite_inner_chart C a t ->
  @is_euclidean_submanifold R N d 1 (p @` M) ->S `<=` M ->
  is_measure_m_rectifiable (@hausdorff_measure R (inner_metric_space hB) d) d S ->
  @borel_set (inner_metric_space hB) S ->
  is_measure_m_rectifiable (@hausdorff_measure R (inner_metric_space hC) q) q T ->
  @borel_set (inner_metric_space hC) T ->
  (q<=d)%N ->(0<=j)%R ->0<=lambda ->
  (exists L,@is_metric_lipschitz_bound R (inner_metric_space hB) (inner_metric_space hC) S F L) ->
  (forall x,S x ->T (F x)) ->
  (forall x,S x ->exists D:Hom (R_n R N) (R_n R K),
    has_norm_differential (inner_norm (@euclidean_inner_productP R N))
      (inner_norm (@euclidean_inner_productP R K)) (fun _=>True)
      (fun z=>t (F (e z))) (p x) D /\
    is_partial_exterior_norm q
      (partial_function_source_restrict
        (norm_tangent_cone (inner_norm (@euclidean_inner_productP R N)) (p @` M) (p x))
        (partial_function_total D)) j) ->
  (forall y,T y ->@hausdorff_measure R (inner_metric_space hB) (d-q)
    [set x|S x /\F x=y]=lambda) ->
  j%:E* @hausdorff_measure R (inner_metric_space hB) d S=
    lambda* @hausdorff_measure R (inner_metric_space hC) q T.
Proof.
move=>hChart hTarget hM hSM hRectS hBorelS hRectT hBorelT hDim hj hLambda hLip hImage hDiff hMass.
pose X:=inner_metric_space (@euclidean_inner_productP R N).
pose Y:=inner_metric_space (@euclidean_inner_productP R K).
pose W:=p @` S.
pose Z:=t @` T.
pose G:=fun z:R_n R N=>t (F (e z)).
pose f:=partial_function_source_restrict W (partial_function_total G).
have hRW:=@finite_inner_chart_measure_rectifiable_coordinates R V B hB N e p d S hChart hRectS.
have hRZ:=@finite_inner_chart_measure_rectifiable_coordinates R U C hC K a t q T hTarget hRectT.
have hWB:=@finite_inner_chart_coordinates_borel R V B hB N e p S hChart hBorelS.
have hZB:=@finite_inner_chart_coordinates_borel R U C hC K a t T hTarget hBorelT.
have hW:=borel_regular_borel_measurable (@hausdorff_measure_is_measure R X d)
  (@hausdorff_measure_borel_regular R X d) hWB.
have hZ:=borel_regular_borel_measurable (@hausdorff_measure_is_measure R Y q)
  (@hausdorff_measure_borel_regular R Y q) hZB.
have hDom:partial_function_domain f=W.
  by rewrite /f partial_function_source_restrict_domain partial_function_total_domain setIT.
have hLP:exists L,@is_partial_metric_lipschitz_bound R X Y f L.
  have [L [hL hBound]]:=hLip; exists L; split; first exact hL.
  move=>x y u v [hx <-] [hy <-].
  have hxS:S (e x).
    have [z hz <-]:=hx; by rewrite (finite_inner_chart_right_inverse hChart).
  have hyS:S (e y).
    have [z hz <-]:=hy; by rewrite (finite_inner_chart_right_inverse hChart).
  have h:=hBound (e x) (e y) hxS hyS.
  have hSourceDist:@mdist R (inner_metric_space hB) (e x) (e y)=@mdist R X x y.
    rewrite !inner_metric_distanceE.
    change (inner_norm hB (e x-e y)=inner_norm (@euclidean_inner_productP R N) (x-y)).
    by rewrite -linearB (@finite_inner_chart_norm R V B hB N e p hChart).
  have hTargetDist:@mdist R Y (G x) (G y)=
      @mdist R (inner_metric_space hC) (F (e x)) (F (e y)).
    rewrite !inner_metric_distanceE /G.
    change (inner_norm (@euclidean_inner_productP R K) (t (F (e x))-t (F (e y)))=
      inner_norm hC (F (e x)-F (e y))).
    by rewrite -linearB (@finite_inner_chart_inverse_norm R U C hC K a t hTarget).
  rewrite hTargetDist; by rewrite hSourceDist in h.
have hRange:partial_function_range f `<=` Z.
  move=>z [x [[u hu <-] <-]].
  exists (F u); first exact:hImage u hu.
  by rewrite /G (finite_inner_chart_right_inverse hChart).
have hCoarea:=@federer_3_2_22 R d N q K W Z f hDim hRW hW hRZ hZ hDom hLP hRange.
have hWSubset:W `<=` p @` M.
  move=>z [x hx <-]; by exists x; first exact:hSM x hx.
have hJac:=@submanifold_subset_tangent_jacobian_almost R N K d 1 q (p @` M) W G j
  (leqnn 1) hM hWSubset hRW hW ltac:(move=>z [x hx <-]; exact:hDiff x hx).
have hFibres y:Z y ->@hausdorff_measure R X (d-q) (partial_mapping_fibre f y)=lambda.
  move=>[v hv <-].
  have hSet:partial_mapping_fibre f (t v)=p @` [set x|S x /\F x=v].
    apply/seteqP; split=>z.
    - move=>[[x hx <-] hF].
      exists x; last reflexivity; split; first exact hx.
      have hEq:t (F x)=t v.
        change (t (F (e (p x)))=t v) in hF.
        by rewrite (finite_inner_chart_right_inverse hChart) in hF.
      have hA:=congr1 a hEq.
      by rewrite !(finite_inner_chart_right_inverse hTarget) in hA.
    - move=>[x [hx hFx] <-]; split; first by exists x.
      change (t (F (e (p x)))=t v).
      by rewrite (finite_inner_chart_right_inverse hChart) hFx.
  rewrite hSet (@finite_inner_chart_inverse_hausdorff R V B hB N e p hChart).
  exact:hMass v hv.
have hResult:=@rectifiable_coarea_constant_volumes R d N q K W Z f j lambda
  hCoarea hW hZ hDom hj hLambda hJac hFibres.
rewrite /W /Z
  (@finite_inner_chart_inverse_hausdorff R V B hB N e p hChart)
  (@finite_inner_chart_inverse_hausdorff R U C hC K a t hTarget) in hResult.
exact hResult.
Qed.
