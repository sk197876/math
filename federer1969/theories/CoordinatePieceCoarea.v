(** Federer (1969), 3.2.10, p. 248: complete coarea
    calculation on a coordinate inverse piece. Rademacher,
    the inverse Jacobian identity, area transformation, Fubini
    and the slice area theorem discharge all intermediate hypotheses.
    Apply the erratum, p. 4, book p. 248 lines 21 and 25:
    both corrected complementary measure degrees are m-n. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanLebesgueDimensions EuclideanTargetJacobianMeasurable
  EuclideanSliceJacobianRepresentative CoordinateCoareaImageIntegral CoordinateSliceAreaAlmost
  EuclideanBlockFunctionFubini EuclideanBlockCutoffSections HausdorffMeasure MappingMultiplicity
  PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition PartialProductSections
  PartialZeroExtension ExtendedRealOrderTopology LipschitzUP MeasureUP MeasureAlmostUP
  MeasureAlmostBasic MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence
  MeasureIntegralAlmostEquality ParameterizedIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [coordinate_piece_coarea]: the integral equality
    of Federer 3.2.10, p. 248, in complementary Cartesian
    dimensions. The hypothesis is precisely the actual inverse
    coordinate law on B, with the printed Lipschitz maps
    and measurable B. The proof also covers k=0 and n=0;
    the final numbered wrapper retains m>n as printed. *)
Theorem coordinate_piece_coarea (R:realType) n k
    (f:inner_metric_space (@euclidean_inner_productP R (n+k))->
      inner_metric_space (@euclidean_inner_productP R n))
    (p:Hom (R_n R (n+k)) (R_n R k))
    (u v:inner_metric_space (@euclidean_inner_productP R (n+k))->
      inner_metric_space (@euclidean_inner_productP R (n+k)))
    (B:set (R_n R (n+k))):
  is_metric_lipschitz setT f ->is_metric_lipschitz setT u ->is_metric_lipschitz setT v ->
  measure_measurable (@euclidean_lebesgue_measure R (n+k)) B ->
  (forall x,B x ->u x=euclidean_block_join (f x,p x) /\ v (u x)=x) ->
  exists a,is_measure_subset_integral (@euclidean_lebesgue_measure R (n+k)) B
      (extended_euclidean_target_jacobian f) a /\
    is_measure_integral (@euclidean_lebesgue_measure R n)
      (partial_function_total (fun y=>(@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R (n+k))) k (mapping_fibre f B y)
          :extended_real_line R))) a.
Proof.
move=>hf hu hv hB hCoords.
have [g hG]:=euclidean_slice_jacobian_representative_exists hv.
have [a [hSource hImage]]:=coordinate_coarea_image_integral hf hu hv hB hCoords hG.
exists a; split; first exact hSource.
pose F:=partial_function_zero_extension (0:extended_real_line R) (u @` B)
  (partial_function_total (fun w=>(g w)%:E:extended_real_line R)).
pose P:=partial_function_precompose (@euclidean_block_join R n k) F.
have hFubini:=euclidean_block_function_fubini hImage.
have hSlices:=coordinate_slice_area_integral_almost hu hv hB hCoords hG.
apply:(@measure_integral_almost_equal R _ _ (euclidean_lebesgue_is_measure R n)
  (parameterized_integral (@euclidean_lebesgue_measure R k) (partial_product_vertical_section P))
  _ a hFubini).
apply:(@measure_almost_everywhere_mono R _ _ (euclidean_lebesgue_is_measure R n) _ _ _ hSlices)=>y hy.
pose mass:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (n+k))) k
  (mapping_fibre f B y).
exists mass; split; last by [].
apply:(parameterized_integral_specification (@euclidean_lebesgue_measure R k)
  (partial_product_vertical_section P) y mass).2.
apply:(@measure_integral_graph_equivalent R _ _ _ _ mass _ hy)=>z r.
exact:iff_sym (euclidean_block_cutoff_vertical_graph (u @` B) g y z r).
Qed.
