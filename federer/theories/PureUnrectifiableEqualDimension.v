(** Federer (1969), 3.2.21, p. 257: the equal-
    dimension special case follows from the area formula. The
    image is a countably rectifiable subset of the purely
    unrectifiable target and hence has zero Hausdorff mass. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  LipschitzUP RectifiableSetUP HausdorffMeasure MeasureUP MeasureAlmostUP MeasureAlmostBasic
  PureCountablyRectifiableNull PositiveJacobianNullPreimage BorelAreaSelection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [pure_unrectifiable_equal_dimension_positive_locus_null]:
    the special case mu=m in Federer 3.2.21, p. 257.
    The set of positive actual top Jacobian in f inverse T is
    Lebesgue-null. This helper needs no Borel assumption on T;
    the full sliced theorem will retain the printed Borel hypothesis. *)
Lemma pure_unrectifiable_equal_dimension_positive_locus_null (R : realType) m n
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n)) (T : set (R_n R n)) :
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R m))
    (inner_metric_space (@euclidean_inner_productP R n)) setT f ->
  is_purely_measure_m_unrectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m T ->
  @euclidean_lebesgue_measure R m (positive_euclidean_jacobian_locus f `&` (f @^-1` T))=0.
Proof.
move=> hLip hPure.
pose A := f @^-1` T.
have hImageSub : f @` A `<=` T by move=> y [x hx <-].
have hNull := pure_unrectifiable_lipschitz_image_null hLip hPure hImageSub.
have hPre := positive_jacobian_null_preimage hLip hNull.
apply: (measure_null_subset (euclidean_lebesgue_is_measure R m) _ hPre)=> x [hx hT].
split; first exact hx; exists x; first exact hT; reflexivity.
Qed.
