(** Federer (1969), 3.2.39, p. 275: combine 3.2.3
    and 2.10.10 to identify the image-cost measure with the
    actual source-degree Jacobian measure on Borel source sets. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanMetricCompleteness EuclideanMetricSeparability
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes HausdorffMeasure HausdorffClosedCoverAgreement
  EuclideanAreaFormula JacobianDensityMeasure LipschitzUP NormMetricScaleContinuity
  SuslinSetUP BorelClosedProjection SuslinMultiplicityIntegral BorelImageCoverCost BorelCaratheodoryMeasure
  MeasureUP MeasureIntegralUP MeasureIntegralUniqueness TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [euclidean_jacobian_image_cost_measure]: supporting
    the cited 3.2.3 and 2.10.10 step in Federer 3.2.39,
    p. 275. Both existing theorems integrate the very same
    actual fibre counting function. Integral uniqueness identifies
    their values on the original Borel set, including infinite
    mass and every natural dimension. No image-cost measure
    equality or supplied multiplicity hypothesis is assumed. *)
Lemma euclidean_jacobian_image_cost_measure (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A:
  is_metric_lipschitz setT f ->borel_set A ->
  euclidean_jacobian_measure f A=
    borel_caratheodory_measure
      (borel_image_cover_cost f (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)) A.
Proof.
move=>hLip hA.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose beta:=@hausdorff_measure R Y m.
have hf:continuous (f:X->Y).
  have [L [hL hBound]]:=hLip.
  apply:(@metric_fixed_lipschitz_continuous R X Y f L hBound.1)=>x y.
  exact:hBound.2 x y Logic.I Logic.I.
have hAm:=@euclidean_borel_measurable R m A hA.
have [a [hSource hArea]]:=euclidean_area_formula hLip hAm.
have hValue:a=euclidean_jacobian_measure f A.
  exact:measure_integral_unique hSource (euclidean_jacobian_measure_integral hLip hAm).
have hSuslin:=@metric_borel_suslin R X A hA.
have hCost:=@continuous_suslin_multiplicity_integral R X Y f beta
  (@hausdorff_measure_is_measure R Y m) (@hausdorff_measure_borel_regular R Y m) A
  (@euclidean_metric_complete R m) (@euclidean_metric_separable R m)
  (@metric_hausdorff R Y) hf hSuslin.
rewrite -hValue; exact:measure_integral_unique hArea hCost.
Qed.
