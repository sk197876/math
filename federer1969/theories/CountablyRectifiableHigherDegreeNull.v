(** Federer (1969), 3.4.8(13), p. 335:
    strata of dimension below q have zero H^q
    measure. Reuse finite mass of rectifiable sets,
    3.2.14, pp. 251–252, and dimension comparison,
    2.10.2(1), p. 171, then countable subadditivity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RectifiableSetUP RectifiableFiniteHausdorffMass HausdorffMeasure HausdorffDimensionDrop
  MeasureUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countably_rectifiable_higher_degree_null]: the
    upper-dimensional nullity inference in 3.4.8(13),
    p. 335. Every actual countably d-rectifiable set
    is null at all integer degrees q>d. *)
Theorem countably_rectifiable_higher_degree_null (R:realType) n d q
    (S:set (R_n R n)):
  (d<q)%N ->@is_countably_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n)) d S ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) q S=0%E.
Proof.
move=>hDQ [F [hF [hRect hCover]]];rewrite hCover.
apply:(@measure_null_countable_union R (inner_metric_space (@euclidean_inner_productP R n))
  [the choiceType of set (R_n R n)]
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) q)
  (@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) q)
  F id hF)=>A hA.
exact:(hausdorff_finite_mass_higher_degree_zero hDQ (rectifiable_finite_hausdorff_mass (hRect A hA))).
Qed.
