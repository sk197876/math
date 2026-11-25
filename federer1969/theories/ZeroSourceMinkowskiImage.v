(** Federer (1969), 3.2.38, p. 274: the source dimension
    zero case is an actual counting/area identity, with its positive atom. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions LipschitzUP MeasureUP MeasureBasic MeasureSubsetIntegral MeasureIntegralUniqueness
  EuclideanAreaFormula EuclideanJacobianMeasurable JacobianDensityMeasure PartitionMultiplicityIntegral
  HausdorffMeasure HausdorffCountingMeasure CountingMeasure MinkowskiContents MinkowskiZeroCounting.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [zero_source_minkowski_image_jacobian_identity]: the
    zero-dimensional boundary of Federer 3.2.38, p. 274. The
    unique source point makes every original map injective. The
    already proved area theorem 3.2.3 and the actual counting
    equality for both degree-zero contents give exact equality
    with the original partial Jacobian integral. Positive atoms
    are retained; no positive source-dimension convention is added. *)
Lemma zero_source_minkowski_image_jacobian_identity (R:realType) n
    (f:inner_metric_space (@euclidean_inner_productP R 0)->
      inner_metric_space (@euclidean_inner_productP R n))
    (C:set (inner_metric_space (@euclidean_inner_productP R 0))):
  is_metric_lipschitz setT f ->measure_measurable (@euclidean_lebesgue_measure R 0) C ->
  upper_minkowski_content 0 (f @` C)=euclidean_jacobian_measure f C.
Proof.
move=>hLip hC.
pose X:=inner_metric_space (@euclidean_inner_productP R 0).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose beta:=@hausdorff_measure R Y 0.
have hb:=@hausdorff_measure_is_measure R Y 0.
have hInj:{in C &,injective f}.
  move=>x y _ _ _; by rewrite (@coordinate_zero R x) (@coordinate_zero R y).
have hCounting:beta=@counting_measure R Y.
  apply:funext=>S; exact:hausdorff_zero_counting_measure.
have hImageMeas:measure_measurable beta (f @` C).
  rewrite hCounting; exact:counting_measure_measurable.
have hImageIntegral:=@injective_multiplicity_integral R X Y f C beta hb hInj hImageMeas.
have [a [hAreaSource hAreaImage]]:=euclidean_area_formula hLip hC.
have hDensityIntegral:=euclidean_jacobian_measure_integral hLip hC.
have hSourceEquality:=measure_integral_unique hAreaSource hDensityIntegral.
have hImageEquality:=measure_integral_unique hAreaImage hImageIntegral.
rewrite (zero_minkowski_contents_counting (f @` C)).1 -hCounting.
by rewrite -hSourceEquality hImageEquality.
Qed.
