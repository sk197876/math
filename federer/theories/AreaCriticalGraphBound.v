(** Federer (1969), 3.2.3, p. 244: the graph
    regularization bounds the Hausdorff measure of the image
    of a critical set by epsilon (M+epsilon)^(m-1) L^m(A).
    The projection is nonexpanding and every differential of
    the graph is injective. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  NormMetricScaleContinuity NormDifferentialUP NormDifferentialDirectional NormDifferentialLipschitzBound
  EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanMetricProduct MetricCartesianProductUP
  EuclideanGraphLift EuclideanGraphLipschitz EuclideanGraphJacobian EuclideanJacobianRank
  EuclideanLinearJacobian LinearJacobianSandwich EuclideanJacobianMeasurable JacobianUP Jacobian
  EuclideanLebesgueDimensions EuclideanMetricCompleteness EuclideanMetricSeparability
  MeasureUP BorelRegularMeasureUP TopologicalBorel InjectiveBorelImage
  MeasureIntegralUP MeasureIntegralUniqueness PartialFunctionUP
  InjectiveDifferentialPieceUP JacobianDensityMeasure AreaInjectiveBorel SubsetIntegralConstantBounds
  HausdorffMeasure HausdorffClosedCoverAgreement HausdorffLipschitzImages LipschitzUP
  PartitionMultiplicityIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [critical_set_graph_image_bound]: the
    final graph-image inequality of Federer 3.2.3,
    p. 244. This form allows infinite L^m(A);
    finiteness is used only when epsilon tends to zero. *)
Theorem critical_set_graph_image_bound (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) (A:set (R_n R m)) M e:
  is_metric_lipschitz_bound setT f M ->
  @borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] A ->
  A `<=` singular_differential_locus f -> (0<e)%R ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m (f @` A)<=
    (e*(M+e)^+m.-1)%R%:E*euclidean_lebesgue_measure m A.
Proof.
move=>hM hA hCritical he.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose Z:=inner_metric_space (@euclidean_inner_productP R (n+m)).
pose g:=euclidean_graph_lift f e.
pose beta:=@hausdorff_measure R Z m.
have he0:e!=0%R by rewrite gt_eqF.
have hMe:(0<M+e)%R by have hM0:=hM.1; nra.
have hgb:=euclidean_graph_lipschitz_bound (ltW he) hM.
have hLipG:@is_metric_lipschitz R X Z setT g by exists (M+e)%R.
have hGInjective:injective g:=@euclidean_graph_lift_injective R m n f e he0.
have hGCont:continuous (g:X->Z).
  apply:(@metric_fixed_lipschitz_continuous R X Z g (M+e)%R (ltW hMe)).
  by move=>x y; exact (hgb.2 x y Logic.I Logic.I).
have hAmeas:measure_measurable (@euclidean_lebesgue_measure R m) A.
  exact (borel_regular_borel_measurable (euclidean_lebesgue_is_measure R m)
    (euclidean_lebesgue_borel_regular R m) hA).
have hGLocus:A `<=` InjectiveDifferentialPieceUP.injective_differential_locus g.
  move=>a ha; have [L [hL hSing]]:=hCritical a ha.
  exists (euclidean_linear_graph_lift L e); split.
  - exact (euclidean_graph_lift_differential e hL).
  - exact (@euclidean_linear_graph_injective R m n L e he0).
have hArea:=area_formula_injective_borel hLipG hA hGLocus.
have hImageB:@borel_set [the topologicalType of Z] (g @` A).
  apply:(@injective_borel_image_borel R X Z g A (@euclidean_metric_complete R m)
    (@euclidean_metric_separable R m) (@metric_hausdorff R Z) hGCont hA).
  by move=>x y hx hy heq; exact (hGInjective x y heq).
have hImageMeas:measure_measurable beta (g @` A).
  exact (borel_regular_borel_measurable (@hausdorff_measure_is_measure R Z m)
    (@hausdorff_measure_borel_regular R Z m) hImageB).
have hImageI:=@injective_multiplicity_integral R X Z g A beta (@hausdorff_measure_is_measure R Z m)
  (fun x y hx hy heq=>hGInjective x y heq) hImageMeas.
have hValue:euclidean_jacobian_measure g A=beta (g @` A):=measure_integral_unique hArea hImageI.
have hc:(0<e^+m)%R:=exprn_gt0 m he.
have hC:(0<e*(M+e)^+m.-1)%R:=mulr_gt0 he (exprn_gt0 m.-1 hMe).
have hBound a j:A a -> partial_function_graph (extended_euclidean_jacobian g) a j ->
    (e^+m)%R%:E<=j /\ j<=(e*(M+e)^+m.-1)%R%:E.
  move=>ha [r [hr <-]].
  have [L [hL hSing]]:=hCritical a ha.
  have [T [hT hJ]]:=(euclidean_jacobian_graph m setT g a r).1 hr.
  have hGD:=euclidean_graph_lift_differential e hL.
  have hEqual:T=euclidean_linear_graph_lift L e.
    exact (norm_differential_unique (inner_norm_real_norm (@euclidean_inner_productP R m))
      (inner_norm_real_norm (@euclidean_inner_productP R (n+m))) hT hGD).
  have hLBound v:(inner_norm (@euclidean_inner_productP R n) (L v)<=
      M*inner_norm (@euclidean_inner_productP R m) v)%R.
    apply:(norm_differential_global_lipschitz_bound
      (inner_norm_real_norm (@euclidean_inner_productP R m))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) hL)=>x y.
    exact (hM.2 x y Logic.I Logic.I).
  have hLower v:(e*inner_norm (@euclidean_inner_productP R m) v<=
      inner_norm (@euclidean_inner_productP R (n+m)) (euclidean_linear_graph_lift L e v))%R.
    have hh:=euclidean_linear_graph_lower_bound L e v; by rewrite (ger0_norm (ltW he)) in hh.
  have hUpper v:(inner_norm (@euclidean_inner_productP R (n+m)) (euclidean_linear_graph_lift L e v)<=
      (M+e)*inner_norm (@euclidean_inner_productP R m) v)%R.
    have hh:=euclidean_graph_lift_norm_bound L e v.
    rewrite (ger0_norm (ltW he)) in hh.
    apply:le_trans hh _; rewrite mulrDl; exact (lerD (hLBound v) (lexx _)).
  have hLo:=(euclidean_top_jacobian_sandwich (ltW he) (ltW hMe) hLower hUpper).1.
  have hHi:=euclidean_singular_graph_jacobian_bound he hM.1 hLBound hSing.
  rewrite hEqual in hJ; rewrite -hJ.
  split; rewrite lee_fin; [exact hLo|exact hHi].
have hJacI:=euclidean_jacobian_measure_integral hLipG hAmeas.
have hJacBound:=(@subset_integral_constant_bounds R X _ (euclidean_lebesgue_is_measure R m) A
  (extended_euclidean_jacobian g) _ (e^+m)%R (e*(M+e)^+m.-1)%R hAmeas hc hC hBound hJacI).2.
rewrite hValue in hJacBound.
pose p:=fun z:Z=>(euclidean_block_split z).1.
have hp:=metric_product_first_nonexpanding (@euclidean_blocks_are_metric_product R n m).
have hPImage:p @` (g @` A)=f @` A.
  have hPg x:p (g x)=f x:=euclidean_graph_lift_first f e x.
  apply/seteqP; split=>y.
  - move=>[z [x hx <-] <-]; rewrite hPg; by exists x.
  - move=>[x hx <-]; exists (g x); last exact (hPg x).
    by exists x.
have hProj:=@hausdorff_lipschitz_image_bound R Z Y p 1%R m hp (g @` A).
rewrite hPImage expr1n mul1e in hProj.
exact (le_trans hProj hJacBound).
Qed.
