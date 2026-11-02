(** Federer (1969), 3.2.32, p. 270: obtain the
    Borel target cover from the actual thresholds of 3.2.31. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP
  MeasureUP HausdorffMeasure HausdorffClosedCoverAgreement HausdorffFibreCutoffs RectifiableSetUP
  MappingMultiplicity ExtendedRealOrderTopology PositiveFibreTargetCoverUP PositiveFibreTargetCoverExistence RectifiableFibreThreshold.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_positive_fibre_cover_exists]: the
    reciprocal-threshold application of Federer 3.2.31 in
    3.2.32, p. 270. The exact positive-fibre locus
    is covered by disjoint finite rectifiable Borel pieces
    with null excess. No cover is assumed or selected globally. *)
Theorem rectifiable_positive_fibre_cover_exists (R:realType) m n mu v
    (W:set (R_n R n)) (F:R_n R n->R_n R v):
  (mu<=m)%N ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R v)) setT F ->
  exists D,@is_positive_fibre_target_cover R (inner_metric_space (@euclidean_inner_productP R v))
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R v)) mu) mu
    [set y|0<@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n))
      (m-mu) (mapping_fibre F W y)] D.
Proof.
move=>hDim hRect hW [L [hL hBound]].
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose T:=inner_metric_space (@euclidean_inner_productP R v).
pose B:=@hausdorff_measure R T mu.
apply:(@positive_fibre_target_cover_exists R T B (@hausdorff_measure_is_measure R T mu)
  (@hausdorff_measure_borel_regular R T mu) mu
  (fun y=>(@hausdorff_measure R X (m-mu) (mapping_fibre F W y):extended_real_line R))).
move=>t ht.
have hThreshold:=@rectifiable_fibre_threshold_rectifiable R n v F W m mu L t hDim ht hRect hW hBound.
exact hThreshold.
Qed.
