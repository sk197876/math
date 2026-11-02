(** Federer (1969), 3.2.28(4), pp. 266–267:
    the area formula on compact rectifiable subsets
    of an actual finite-dimensional manifold. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric
  FiniteInnerChartUP FiniteInnerChartCompact FiniteInnerChartFibres FiniteInnerTangentIsometryChart
  EuclideanSubmanifoldUP CompactSubmanifoldRectifiable SubmanifoldSubsetTangentJacobian
  NormDifferentialUP TangentConeUP PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  PartialMetricLipschitz PartialMappingMultiplicity LipschitzUP NormMetricScaleContinuity
  MeasureUP HausdorffMeasure HausdorffClosedCoverAgreement BorelRegularMeasureUP TopologicalBorel
  RectifiableAreaConstantMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_inner_compact_tangent_area]: actual
    tangent isometry and constant actual fibre count
    give the compact-piece area identity, supporting
    Federer 3.2.28(4), pp. 266–267. The
    piece is not assumed to be a submanifold. *)
Theorem finite_inner_compact_tangent_area (R:realType) (V U:lmodType R)
    (B:V->V->R) (C:U->U->R) (hB:is_inner_product B) (hC:is_inner_product C) N M mu k
    (e:Hom (R_n R N) V) (p:Hom V (R_n R N))
    (a:Hom (R_n R M) U) (t:Hom U (R_n R M))
    (S K:set V) (F:V->U) (r : \bar R):
  is_finite_inner_chart B e p ->is_finite_inner_chart C a t ->(1<=k)%N ->
  @is_euclidean_submanifold R N mu k (p @` S) ->K `<=` S ->
  @compact [the topologicalType of inner_metric_space hB] K ->
  @compact [the topologicalType of inner_metric_space hC] (F @` K) ->
  (exists L,@is_metric_lipschitz_bound R (inner_metric_space hB) (inner_metric_space hC) K F L) ->
  (forall x,K x ->exists D:Hom V U,
    has_norm_differential (inner_norm hB) (inner_norm hC) (fun _=>True) F x D /\
    forall v w,norm_tangent_cone (inner_norm hB) S x v ->
      norm_tangent_cone (inner_norm hB) S x w ->C (D v) (D w)=B v w) ->
  0<=r ->(forall y,(F @` K) y ->@CountingMeasure.counting_measure R V [set x|K x /\F x=y]=r) ->
  @hausdorff_measure R (inner_metric_space hB) mu K=
    r* @hausdorff_measure R (inner_metric_space hC) mu (F @` K).
Proof.
move=>hChart hTarget hk hS hKS hCK hCFK hLip hDiff hr hCount.
pose X:=inner_metric_space (@euclidean_inner_productP R N).
pose Y:=inner_metric_space (@euclidean_inner_productP R M).
pose W:=p @` K.
pose Z:=t @` (F @` K).
pose G:=fun z:R_n R N=>t (F (e z)).
pose f:=partial_function_source_restrict W (partial_function_total G).
have hCW:=@finite_inner_chart_compact R V B hB N e p K hChart hCK.
have hCZ:=@finite_inner_chart_compact R U C hC M a t (F @` K) hTarget hCFK.
have hSub:W `<=` p @` S.
  move=>z [x hx <-]; exists x; first exact:hKS x hx.
  reflexivity.
have hRect:=compact_submanifold_measure_rectifiable hk hS hSub hCW.
have hW:measure_measurable (@hausdorff_measure R X mu) W.
  apply:(borel_regular_borel_measurable (@hausdorff_measure_is_measure R X mu)
    (@hausdorff_measure_borel_regular R X mu)).
  apply:closed_borel_set; exact:compact_closed (@metric_hausdorff R X) hCW.
have hZ:measure_measurable (@hausdorff_measure R Y mu) Z.
  apply:(borel_regular_borel_measurable (@hausdorff_measure_is_measure R Y mu)
    (@hausdorff_measure_borel_regular R Y mu)).
  apply:closed_borel_set; exact:compact_closed (@metric_hausdorff R Y) hCZ.
have hDom:partial_function_domain f=W.
  by rewrite /f partial_function_source_restrict_domain partial_function_total_domain setIT.
have hLP:exists L,@is_partial_metric_lipschitz_bound R X Y f L.
  have [L [hL hBound]]:=hLip; exists L; split; first exact hL.
  move=>x y u v [hx <-] [hy <-].
  have hxS:K (e x).
    have [z hz <-]:=hx; by rewrite (finite_inner_chart_right_inverse hChart).
  have hyS:K (e y).
    have [z hz <-]:=hy; by rewrite (finite_inner_chart_right_inverse hChart).
  have h:=hBound (e x) (e y) hxS hyS.
  have hSourceDist:@mdist R (inner_metric_space hB) (e x) (e y)=@mdist R X x y.
    rewrite !inner_metric_distanceE.
    change (inner_norm hB (e x-e y)=inner_norm (@euclidean_inner_productP R N) (x-y)).
    by rewrite -linearB (@finite_inner_chart_norm R V B hB N e p hChart).
  have hTargetDist:@mdist R Y (G x) (G y)=
      @mdist R (inner_metric_space hC) (F (e x)) (F (e y)).
    rewrite !inner_metric_distanceE /G.
    change (inner_norm (@euclidean_inner_productP R M) (t (F (e x))-t (F (e y)))=
      inner_norm hC (F (e x)-F (e y))).
    by rewrite -linearB (@finite_inner_chart_inverse_norm R U C hC M a t hTarget).
  rewrite hTargetDist; by rewrite hSourceDist in h.
have hRange:partial_function_range f `<=` Z.
  move=>z [x [[u hu <-] <-]].
  exists (F u); first by exists u.
  by rewrite /G (finite_inner_chart_right_inverse hChart).
have hOrth:OrthogonalMaps.is_orthogonal_map C (@euclidean_inner_product R M) (hom_as_linear t).
  move=>x y; exact:(@finite_inner_chart_inverse_product R U C M a t hTarget x y).
have hValues z:W z ->exists D:Hom (R_n R N) (R_n R M),
    has_norm_differential (inner_norm (@euclidean_inner_productP R N))
      (inner_norm (@euclidean_inner_productP R M)) (fun _=>True) G z D /\
    forall v w,norm_tangent_cone (inner_norm (@euclidean_inner_productP R N)) (p @` S) z v ->
      norm_tangent_cone (inner_norm (@euclidean_inner_productP R N)) (p @` S) z w ->
      euclidean_inner_product (D v) (D w)=euclidean_inner_product v w.
  move=>[x hx <-]; have [D [hD hPair]]:=hDiff x hx.
  exists (hom_comp t (hom_comp D e)).
  exact:(@finite_inner_tangent_isometry_chart R V U B C hB hC N M e p t S F x D hChart hOrth hD hPair).
have hJac:=@submanifold_subset_tangent_isometry_jacobian_one R N M mu k (p @` S) W G
  hk hS hSub hRect hW hValues.
have hMult z:Z z ->@partial_mapping_multiplicity R _ _ f z=r.
  move=>[y hy <-].
  rewrite /f /G (@finite_inner_chart_fibre_multiplicity R V U B C hB N M e p a t K F y hChart hTarget).
  exact:hCount y hy.
have hResult:=@rectifiable_area_constant_multiplicity R mu N M W Z f 1%R r
  hRect hW hZ hDom hLP hRange ler01 hr hJac hMult.
rewrite mul1e /W /Z
  (@finite_inner_chart_inverse_hausdorff R V B hB N e p hChart)
  (@finite_inner_chart_inverse_hausdorff R U C hC M a t hTarget) in hResult.
exact hResult.
Qed.
