(** Federer (1969), 3.2.8, p. 247: a
    Lipschitz self-map of Euclidean space preserves
    Lebesgue null sets, by 2.10.11, p. 176,
    and 2.10.35, p. 197. This supplies
    null transport for the inverse differential domain. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanHausdorffLebesgue HausdorffMeasure LipschitzUP NullLipschitzArea.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_lipschitz_selfmap_null_image]:
    the null-image step in the definition of S
    in Federer 3.2.8, p. 247. No
    measurability of the original null set is needed;
    the exact natural-degree Hausdorff normalization is used. *)
Lemma euclidean_lipschitz_selfmap_null_image (R:realType) m
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R m)) A:
  is_metric_lipschitz setT f ->
  euclidean_lebesgue_measure m A=0%E ->
  euclidean_lebesgue_measure m (f @` A)=0%E.
Proof.
move=>[L [hL hBound]] hA.
have hH:@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) m A=0%E.
  by rewrite (euclidean_hausdorff_spherical_lebesgue A).1.
have hImage:=null_hausdorff_lipschitz_image hBound hH.
by rewrite (euclidean_hausdorff_spherical_lebesgue (f @` A)).1 in hImage.
Qed.
