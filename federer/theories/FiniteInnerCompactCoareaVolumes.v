(** Federer (1969), 3.2.28(2),(3), pp. 265–266:
    coarea on the actual compact inner-product manifolds,
    through orthonormal Euclidean ambient coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric
  FiniteInnerChartUP FiniteInnerChartCompact EuclideanSubmanifoldUP NormDifferentialUP TangentConeUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialMetricLipschitz
  PartialMappingMultiplicity PartialExteriorNormUP LipschitzUP MeasureUP HausdorffMeasure
  RectifiableCoarea RectifiableCoareaConstantVolumes SubmanifoldTangentJacobian.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_inner_compact_coarea_volumes]: the
    two actual coarea volume identities of Federer
    3.2.28(2),(3), pp. 265–266, by
    3.2.22, pp. 258–260. This supporting
    specialization requires actual coordinate differentials,
    tangent exterior norms and actual fibre measures;
    no volume equality is a premise. *)
Theorem finite_inner_compact_coarea_volumes (R:realType)
    (V U:lmodType R) (B:V->V->R) (C:U->U->R)
    (hB:is_inner_product B) (hC:is_inner_product C) N K d q
    (e:Hom (R_n R N) V) (p:Hom V (R_n R N))
    (a:Hom (R_n R K) U) (t:Hom U (R_n R K))
    (S:set V) (T:set U) (F:V->U) (j:R) (lambda : \bar R):
  is_finite_inner_chart B e p ->is_finite_inner_chart C a t ->
  @is_euclidean_submanifold R N d 1 (p @` S) ->
  @is_euclidean_submanifold R K q 1 (t @` T) ->
  @compact [the topologicalType of inner_metric_space hB] S ->
  @compact [the topologicalType of inner_metric_space hC] T ->
  (q<=d)%N ->(0<=j)%R ->0<=lambda ->
  (exists L,@is_metric_lipschitz_bound R (inner_metric_space hB) (inner_metric_space hC) S F L) ->
  (forall x,S x ->T (F x)) ->
  (forall x,S x ->exists D:Hom (R_n R N) (R_n R K),
    has_norm_differential (inner_norm (@euclidean_inner_productP R N))
      (inner_norm (@euclidean_inner_productP R K)) (fun _=>True)
      (fun z=>t (F (e z))) (p x) D /\
    is_partial_exterior_norm q
      (partial_function_source_restrict
        (norm_tangent_cone (inner_norm (@euclidean_inner_productP R N)) (p @` S) (p x))
        (partial_function_total D)) j) ->
  (forall y,T y ->@hausdorff_measure R (inner_metric_space hB) (d-q)
    [set x|S x /\F x=y]=lambda) ->
  j%:E* @hausdorff_measure R (inner_metric_space hB) d S=
    lambda* @hausdorff_measure R (inner_metric_space hC) q T.
Proof.
move=>hChart hTarget hS hT hCompactS hCompactT hDim hj hLambda hLip hImage hDiff hMass.
pose X:=inner_metric_space (@euclidean_inner_productP R N).
pose Y:=inner_metric_space (@euclidean_inner_productP R K).
pose W:=p @` S.
pose Z:=t @` T.
pose G:=fun z:R_n R N=>t (F (e z)).
pose f:=partial_function_source_restrict W (partial_function_total G).
have [hRW hW]:=@finite_inner_chart_compact_manifold_measure R V B hB N d 1 e p S
  hChart (leqnn 1) hS hCompactS.
have [hRZ hZ]:=@finite_inner_chart_compact_manifold_measure R U C hC K q 1 a t T
  hTarget (leqnn 1) hT hCompactT.
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
have hJac:=@submanifold_tangent_jacobian_almost R N K d 1 q W G j
  (leqnn 1) hS hRW hW ltac:(move=>z [x hx <-]; exact:hDiff x hx).
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
