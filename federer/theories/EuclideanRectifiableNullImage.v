(** Federer (1969), 3.2.19, p. 256: 2.10.11 transports
    the exceptional Lebesgue-null source sets to Hausdorff-null chart
    images. The source Hausdorff measure equals its Lebesgue measure. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP
  EuclideanLebesgueDimensions EuclideanHausdorffLebesgue HausdorffMeasure HausdorffLipschitzImages
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_lipschitz_null_image]: the use of 2.10.11
    in Federer 3.2.19, p. 256. No source-set measurability,
    target-set measurability or positive dimension premise is added. *)
Theorem euclidean_lipschitz_null_image (R : realType) m n
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n))
    (A : set (R_n R m)) :
  is_metric_lipschitz setT f -> euclidean_lebesgue_measure m A=0 ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m (f @` A)=0.
Proof.
move=> [L [hL hBound]] hNull.
have hh := hausdorff_lipschitz_image_bound m hBound A.
rewrite (euclidean_hausdorff_spherical_lebesgue A).1 hNull mule0 in hh.
apply/eqP; rewrite eq_le hh (measure_nonnegative (@hausdorff_measure_is_measure R _ m)); reflexivity.
Qed.
