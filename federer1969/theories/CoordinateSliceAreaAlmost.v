(** Federer (1969), 3.2.10, p. 248: the inner
    integrals over projected fibres equal their actual Hausdorff
    masses almost everywhere. Prove source section measurability
    and derive the differential representative rather than assuming them. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanLebesgueDimensions EuclideanBlockImageSections
  CoordinateInverseFibres CoordinateImageSections MappingMultiplicity ProductSections
  EuclideanSliceDifferentials EuclideanSliceJacobianRepresentative EuclideanSliceJacobianAlmost
  InjectiveAreaMass HausdorffMeasure LipschitzUP RealMetricBackground ExtendedRealOrderTopology
  PartialFunctionBasic MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureSubsetIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [coordinate_slice_area_integral_almost]: the
    final inner-integral equality of Federer 3.2.10, p. 248.
    For almost every y, integrate the measurable Jacobian
    representative over the actual vertical section of u(B).
    The result is H^k(B intersect f inverse y), with
    infinite mass allowed and no extra slicing hypothesis. *)
Theorem coordinate_slice_area_integral_almost (R:realType) n k
    (f:R_n R (n+k)->R_n R n) (p:R_n R (n+k)->R_n R k)
    (u v:inner_metric_space (@euclidean_inner_productP R (n+k))->
      inner_metric_space (@euclidean_inner_productP R (n+k)))
    (B:set (R_n R (n+k))) (g:R_n R (n+k)->real_line_metric R):
  is_metric_lipschitz setT u ->is_metric_lipschitz setT v ->
  measure_measurable (@euclidean_lebesgue_measure R (n+k)) B ->
  (forall x,B x ->u x=euclidean_block_join (f x,p x) /\ v (u x)=x) ->
  is_euclidean_slice_jacobian_representative v g ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R n)
    [set y|is_measure_subset_integral (@euclidean_lebesgue_measure R k)
      (product_vertical_section ((@euclidean_block_join R n k) @^-1` (u @` B)) y)
      (partial_function_total (fun z=>(g (euclidean_block_join (y,z)))%:E:extended_real_line R))
      (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (n+k))) k
        (mapping_fibre f B y))].
Proof.
move=>hu hv hB hCoords hG.
have hMeas:=euclidean_block_image_sections_measurable hu hB.
have hJac:=euclidean_slice_jacobian_representative_almost hv hG.
apply:(@measure_almost_everywhere_mono R _ _ (euclidean_lebesgue_is_measure R n) _ _ _
  (measure_almost_everywhere_and (euclidean_lebesgue_is_measure R n) hMeas hJac))=>y [hCy hJy].
pose C:=product_vertical_section ((@euclidean_block_join R n k) @^-1` (u @` B)) y.
pose vy:=fun z=>v (euclidean_block_join (y,z)).
have hU x:B x ->u x=euclidean_block_join (f x,p x) by move=>hx; exact (hCoords x hx).1.
have hC:C=p @` mapping_fibre f B y:=coordinate_image_vertical_section hU y.
have hInj:{in C &,injective vy}.
  move=>z w hz hw he.
  have hz':(p @` mapping_fibre f B y) z by rewrite -hC; exact (set_mem hz).
  have hw':(p @` mapping_fibre f B y) w by rewrite -hC; exact (set_mem hw).
  exact (coordinate_inverse_fibre_slice_injective hCoords hz' hw' he).
have hI:=euclidean_injective_area_mass_representative
  (euclidean_slice_lipschitz hv y) hCy hInj hJy.
have hImage:vy @` C=mapping_fibre f B y:=coordinate_image_slice_mass_set hCoords y.
by rewrite hImage in hI.
Qed.
