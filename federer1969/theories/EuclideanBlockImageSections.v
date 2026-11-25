(** Federer (1969), 3.2.10, p. 248: measurable
    sections of a Lipschitz image of a Lebesgue-measurable set.
    Use the already proved measurable-image law and Fubini,
    with the exact block measure of 2.6.5, p. 120. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes EuclideanHausdorffLebesgue HausdorffMeasure
  EuclideanBlockCoordinates EuclideanBlockMeasure LipschitzUP LipschitzMeasurableImages
  MeasureUP MeasurePushforward PushforwardMeasurableSets CountablyMeasurableUP
  CountablyMeasurableSubsets CountablyMeasurableProduct ProductMeasure ProductSections
  ProductSetFubini MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [euclidean_block_image_measurable]: the image
    domain in the Fubini step of Federer 3.2.10,
    p. 248, is product measurable. Neither injectivity nor
    finiteness of B is needed for this supporting assertion. *)
Lemma euclidean_block_image_measurable (R:realType) n k
    (u:inner_metric_space (@euclidean_inner_productP R (n+k))->
      inner_metric_space (@euclidean_inner_productP R (n+k)))
    (B:set (R_n R (n+k))):
  is_metric_lipschitz setT u ->measure_measurable (@euclidean_lebesgue_measure R (n+k)) B ->
  measure_measurable (product_measure (euclidean_lebesgue_is_measure R n)
    (euclidean_lebesgue_is_measure R k))
    ((@euclidean_block_join R n k) @^-1` (u @` B)).
Proof.
move=>hu hB.
have hImage:=euclidean_lipschitz_measurable_image hu hB.
have hMeasures:(@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (n+k))) (n+k))=
    (@euclidean_lebesgue_measure R (n+k)).
  apply:funext=>A; exact (euclidean_hausdorff_spherical_lebesgue A).1.
rewrite hMeasures in hImage.
rewrite -euclidean_block_measure.
apply:pushforward_measurable_from_preimage.
have he:(@euclidean_block_split R n k) @^-1`
    ((@euclidean_block_join R n k) @^-1` (u @` B))=u @` B.
  apply:funext=>x.
  change ((u @` B) (euclidean_block_join (euclidean_block_split x))=(u @` B) x).
  by rewrite euclidean_block_splitK.
by rewrite he.
Qed.

(** Source for [euclidean_block_image_sections_measurable]:
    the measurable projected slice domains in Federer 3.2.10,
    p. 248. Euclidean sigma finiteness is proved by the
    existing measure interface, so it is not an extra hypothesis. *)
Theorem euclidean_block_image_sections_measurable (R:realType) n k
    (u:inner_metric_space (@euclidean_inner_productP R (n+k))->
      inner_metric_space (@euclidean_inner_productP R (n+k)))
    (B:set (R_n R (n+k))):
  is_metric_lipschitz setT u ->measure_measurable (@euclidean_lebesgue_measure R (n+k)) B ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R n)
    [set y|measure_measurable (@euclidean_lebesgue_measure R k)
      (product_vertical_section ((@euclidean_block_join R n k) @^-1` (u @` B)) y)].
Proof.
move=>hu hB.
have hMeas:=euclidean_block_image_measurable hu hB.
have hCount:measure_countably_measurable
    (product_measure (euclidean_lebesgue_is_measure R n) (euclidean_lebesgue_is_measure R k))
    ((@euclidean_block_join R n k) @^-1` (u @` B)).
  apply:(measurable_subset_countably_measurable (product_measure_is_measure _ _) hMeas (subsetT _)).
  exact (@product_whole_countably_measurable R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
    [the choiceType of inner_metric_space (@euclidean_inner_productP R k)]
    (@euclidean_lebesgue_measure R n) (@euclidean_lebesgue_measure R k)
    (euclidean_lebesgue_is_measure R n) (euclidean_lebesgue_is_measure R k)
    (euclidean_lebesgue_countably_measurable R n) (euclidean_lebesgue_countably_measurable R k)).
exact (@product_set_fubini R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
  [the choiceType of inner_metric_space (@euclidean_inner_productP R k)]
  (@euclidean_lebesgue_measure R n) (@euclidean_lebesgue_measure R k)
  (euclidean_lebesgue_is_measure R n) (euclidean_lebesgue_is_measure R k) _ hCount).1.
Qed.
