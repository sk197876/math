(** The coordinate-line tests in Federer (1969), 2.5.10, p. 101, using
    Hausdorff length from 2.10.2(1), p. 171, its line identification in
    2.10.7, p. 175, and the image inequality in 2.10.11, p. 176. No local
    correction is made. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals
  constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RealMetricBackground EuclideanCoordinateMetric HausdorffLength HausdorffLengthMaps
  HausdorffLengthReal LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [hausdorff_coordinate_line_measure]:
    supporting line-measure identity for the horizontal and
    vertical tests in Federer 2.5.10, p. 101.
    The equality follows from 2.10.7, p. 175,
    and nonexpanding maps in both directions, and holds
    for arbitrary subsets of the parameter line. *)
Theorem hausdorff_coordinate_line_measure (R : realType) n (i : 'I_n)
    (v : inner_metric_space (@euclidean_inner_productP R n)) (A : set R) :
  hausdorff_length (euclidean_coordinate_line i v @` A)=lebesgue_scalar_measure A.
Proof.
have he := @hausdorff_length_retracted_isometry R
  [the metricType R of real_line_metric R]
  [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]
  (euclidean_coordinate_line i v) (euclidean_coordinate_retraction i v).
have hf : forall s t, mdist (euclidean_coordinate_line i v s)
    (euclidean_coordinate_line i v t)<=mdist s t.
  by move=> s t; rewrite euclidean_coordinate_line_distance.
have hg := @euclidean_coordinate_retraction_nonexpanding R n i v.
have h := he hf hg (@euclidean_coordinate_line_retraction R n i v) A.
by rewrite hausdorff_length_real_eq_lebesgue in h.
Qed.

(** Source for [hausdorff_coordinate_segment_measure]:
    finite line-segment tests for the geometric example in
    Federer 2.5.10, p. 101, from the segment
    length law of 2.5.17, p. 111, and
    2.10.7, p. 175. Point segments are included. *)
Corollary hausdorff_coordinate_segment_measure (R : realType) n (i : 'I_n)
    (v : inner_metric_space (@euclidean_inner_productP R n)) (a b : R) : a<=b ->
  hausdorff_length (euclidean_coordinate_line i v @` `[a,b])=(b-a)%:E.
Proof. by move=> hab; rewrite hausdorff_coordinate_line_measure lebesgue_scalar_segment. Qed.
