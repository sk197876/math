(** Federer (1969), 3.2.36, p. 273:
    apply actual distance coarea to the
    positive first-distance portion of the product tube. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates
  EuclideanOneCoordinate EuclideanCartesianMap CompactSetDistanceProfile CompactHausdorffMetric
  EuclideanFirstCylinderDistance EuclideanDistanceSubsetCoarea EuclideanDistanceStripCoarea
  EuclideanDistanceTubeBasic MetricSetDistanceUP EuclideanLebesgueDimensions TopologicalBorel
  BorelRegularMeasureUP MeasureUP MeasureIntegralUP PartialFunctionBasic MappingMultiplicity
  HausdorffMeasure ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_product_positive_strip_coarea]:
    the positive-first-distance coarea term in
    the first display of Federer 3.2.36,
    p. 273. The actual first-factor
    cylinder is nonempty closed and its
    printed distance has the proved distance
    laws. The source is an open tube
    intersected with its positive-distance strip,
    so all measurability and unit-Jacobian
    obligations are discharged. Positive first
    dimension and arbitrary second dimension
    include the ambient-one counting-fibre case;
    no finite-volume hypothesis is assumed. *)
Theorem euclidean_product_positive_strip_coarea (R:realType) m n
    (A:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R m)))
    (B:set (inner_metric_space (@euclidean_inner_productP R n)))
    (d:inner_metric_space (@euclidean_inner_productP R (m+n))->R) (r:R):
  (0<m)%N ->@is_metric_set_distance R (inner_metric_space (@euclidean_inner_productP R (m+n))) (euclidean_cartesian_set (val A) B) d ->
  let f:=fun z:inner_metric_space (@euclidean_inner_productP R (m+n))=>
    compact_set_distance_profile A (euclidean_block_split z).1 in
  let W:set (inner_metric_space (@euclidean_inner_productP R (m+n))):=
    [set z|0<f z<r] `&` [set z|d z<r] in
  is_measure_integral (@euclidean_lebesgue_measure R 1)
    (partial_function_total (fun y=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R (m+n))) (m+n-1)
      (mapping_fibre (fun z=>euclidean_one_embed (f z)) W y):extended_real_line R)))
    (@euclidean_lebesgue_measure R (m+n) W).
Proof.
move=>hm hD f W.
pose Z:=inner_metric_space (@euclidean_inner_productP R (m+n)).
pose C:set Z:=[set z|val A (euclidean_block_split z).1].
have [hClosed [hNonempty hCylinder]]:=@euclidean_first_cylinder_distance R m n A.
have hPositiveDimension:(0<m+n)%N by rewrite addn_gt0 hm.
have hOpen:open W.
  apply:openI.
  - exact:(@euclidean_distance_strip_open R (m+n) C f 0%R r hCylinder).
  - exact:(@euclidean_distance_tube_open R (m+n) (euclidean_cartesian_set (val A) B) d r hD).
have hMeasurable:measure_measurable (@euclidean_lebesgue_measure R (m+n)) W.
  apply:(borel_regular_borel_measurable (euclidean_lebesgue_is_measure R (m+n))
    (euclidean_lebesgue_borel_regular R (m+n))).
  exact:open_borel_set hOpen.
apply:(@euclidean_distance_subset_coarea R (m+n) C W f r hPositiveDimension hClosed hNonempty hCylinder hMeasurable).
by move=>z [hz _].
Qed.
