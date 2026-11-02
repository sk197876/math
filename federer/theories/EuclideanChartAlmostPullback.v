(** Federer (1969), 3.2.20, p. 257: the image
    exceptional set is Hausdorff-null, while the parameter exceptional
    set is Lebesgue-null. Use the exact Euclidean normalization of 2.10.35. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanHausdorffLebesgue MeasureAlmostUP
  HausdorffMeasure MetricBiLipschitzUP MetricBiLipschitzNullPullback.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [euclidean_chart_almost_pullback]: the Lebesgue
    almost-everywhere interpretation of the first display in Federer
    3.2.20, p. 257. It follows from 2.10.11, p. 176,
    for the actual inverse and H^m=L^m on R^m from 2.10.35,
    p. 197. No arbitrary measurable-preimage assertion is used. *)
Lemma euclidean_chart_almost_pullback (R : realType) m n
    (K : set (R_n R m)) (psi : R_n R m -> R_n R n) (lambda : R)
    (P : set (R_n R n)) :
  @is_metric_bilipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R m))
    (inner_metric_space (@euclidean_inner_productP R n)) K psi lambda ->
  measure_almost_everywhere_on (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) (psi @` K) P ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m) K [set a | P (psi a)].
Proof.
move=> hBi hAE.
have hh := @metric_bilipschitz_almost_pullback R
  (inner_metric_space (@euclidean_inner_productP R m))
  (inner_metric_space (@euclidean_inner_productP R n)) K psi lambda m 0 P hBi hAE.
by rewrite /measure_almost_everywhere_on (euclidean_hausdorff_spherical_lebesgue _).1 in hh.
Qed.
