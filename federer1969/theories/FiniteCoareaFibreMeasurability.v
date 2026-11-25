(** Federer (1969), 3.2.11, p. 249: the
    finite-source fibre mass used in the critical perturbation
    is measurable by 2.10.26. Transport its actual source
    and target Hausdorff measures through the Euclidean equalities. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanHausdorffLebesgue HausdorffMeasure HausdorffFibreCutoffs HausdorffFibreMeasurability
  CoareaNullFibres MappingMultiplicity LipschitzUP MeasureUP MeasureAlmostUP MeasurableFunctionUP
  PartialFunctionBasic ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_coarea_fibre_measurability]: the
    application of 2.10.26 in Federer 3.2.11, p. 249.
    Both measurability of the fibre-mass function and almost
    everywhere measurability of the actual fibre sets are
    obtained from finite measurable source mass, with n<=m
    and the original natural-degree Hausdorff measure. *)
Theorem finite_coarea_fibre_measurability (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A:
  (n<=m)%N ->is_metric_lipschitz setT f ->
  measure_measurable (@euclidean_lebesgue_measure R m) A ->euclidean_lebesgue_measure m A< +oo ->
  is_measure_measurable_function (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun y=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R m)) (m-n) (mapping_fibre f A y)
        :extended_real_line R))) /\
  measure_almost_everywhere (@euclidean_lebesgue_measure R n)
    [set y|measure_measurable (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R m)) (m-n)) (mapping_fibre f A y)].
Proof.
move=>hnm hf hA hFinite.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
have hSource:(@hausdorff_measure R X ((m-n)+n))=(@euclidean_lebesgue_measure R m).
  apply:funext=>S.
  have hDegree:=congr1 (fun d:nat=>@hausdorff_measure R X d S) (subnK hnm).
  by rewrite hDegree (euclidean_hausdorff_spherical_lebesgue S).1.
have hTarget:(@hausdorff_measure R Y n)=(@euclidean_lebesgue_measure R n).
  apply:funext=>S; exact (euclidean_hausdorff_spherical_lebesgue S).1.
have hHMeas:measure_measurable (@hausdorff_measure R X ((m-n)+n)) A.
  by rewrite hSource.
have hHFinite:@hausdorff_measure R X ((m-n)+n) A< +oo.
  by rewrite hSource.
have h:=@federer_2_10_26 R X Y f hf A (m-n) n
  (@coarea_euclidean_source_proper R m) hHMeas hHFinite.
rewrite hTarget in h; exact h.
Qed.
