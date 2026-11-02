(** Federer (1969), 3.2.10, p. 248: justify replacing
    the complementary Jacobian representative by J_k v_y on
    almost every slice. Use Rademacher and the null-section
    case of Fubini, 2.6.2(3), pp. 115, 117. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanBlockMeasure EuclideanLebesgueDimensions
  EuclideanSliceDifferentials EuclideanSliceJacobianRepresentative EuclideanLinearJacobian
  EuclideanJacobianMeasurable Jacobian NormDifferentialUP PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic ProductMeasure ProductSections ProductNullSections
  MeasurePushforward ExtendedRealOrderTopology RealMetricBackground LipschitzUP Rademacher.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_slice_jacobian_representative_almost]:
    the passage to J_(m-n) v_y in Federer 3.2.10,
    p. 248. For almost every y the representative and
    the actual partial slice Jacobian agree almost everywhere
    in z. The exceptional set is derived from Rademacher,
    rather than assumed separately for the chosen coordinates. *)
Theorem euclidean_slice_jacobian_representative_almost (R:realType) m n k
    (v:inner_metric_space (@euclidean_inner_productP R (n+k))->
      inner_metric_space (@euclidean_inner_productP R m))
    (g:R_n R (n+k)->real_line_metric R):
  is_metric_lipschitz setT v ->is_euclidean_slice_jacobian_representative v g ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R n)
    [set y|measure_almost_equal (@euclidean_lebesgue_measure R k)
      (extended_euclidean_jacobian (fun z=>v (euclidean_block_join (y,z))))
      (partial_function_total (fun z=>(g (euclidean_block_join (y,z)))%:E:extended_real_line R))].
Proof.
move=>hv hG.
pose X:=inner_metric_space (@euclidean_inner_productP R (n+k)).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose Z:=inner_metric_space (@euclidean_inner_productP R k).
pose NX:=inner_norm (@euclidean_inner_productP R (n+k)).
pose NT:=inner_norm (@euclidean_inner_productP R m).
pose D:set X:=fun x=>norm_differentiable_at NX NT setT v x.
pose S:set (Y*Z):=fun p=>~D (euclidean_block_join p).
have hNull:product_measure (euclidean_lebesgue_is_measure R n)
    (euclidean_lebesgue_is_measure R k) S=0%E.
  rewrite -euclidean_block_measure /measure_pushforward.
  have he:(@euclidean_block_split R n k) @^-1` S=~` D.
    apply:funext=>x.
    change ((~D (euclidean_block_join (euclidean_block_split x)))=(~D x)).
    by rewrite euclidean_block_splitK.
  rewrite he; exact (federer_3_1_6 hv).
have hSections:=@product_null_vertical_sections R [the choiceType of Y] [the choiceType of Z]
  (@euclidean_lebesgue_measure R n) (@euclidean_lebesgue_measure R k)
  (euclidean_lebesgue_is_measure R n) (euclidean_lebesgue_is_measure R k) S hNull.
apply:(@measure_almost_everywhere_mono R _ _ (euclidean_lebesgue_is_measure R n) _ _ _ hSections)=>y hy.
have hDiff:measure_almost_everywhere (@euclidean_lebesgue_measure R k)
    [set z|norm_differentiable_at NX NT setT v (euclidean_block_join (y,z))].
  exact hy.
apply:(@measure_almost_everywhere_mono R _ _ (euclidean_lebesgue_is_measure R k) _ _ _ hDiff)=>z [M hM].
pose L:=hom_comp M (@euclidean_last_injection_map R n k).
pose j:=euclidean_linear_jacobian k L.
exists (j%:E:extended_real_line R); split.
- exists j; split; last by [].
  apply:(euclidean_jacobian_graph k setT (fun w=>v (euclidean_block_join (y,w))) z j).2.
  exists L; split; last by [].
  exact (euclidean_slice_differential hM).
- change ((g (euclidean_block_join (y,z)))%:E=j%:E).
  by rewrite (hG.2.2 _ M hM).
Qed.
