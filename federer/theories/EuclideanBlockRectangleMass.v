(** Federer (1969), 3.2.33, p. 270: product-measure
    computation supporting the positive source mass; use the
    already proved block identification of 2.6.5, p. 120. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates
  EuclideanLebesgueDimensions EuclideanBlockMeasure MeasureUP MeasurePushforward ProductRectangleValue ProductMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_block_rectangle_mass]: the product
    step H^m(X)=L^1(T minus V) in Federer 3.2.33,
    p. 270. The usual block isomorphism and the proved
    measurable rectangle formula give the exact mass. Empty
    blocks and infinite factor values retain their prior conventions. *)
Lemma euclidean_block_rectangle_mass (R:realType) a b
    (A:set (R_n R a)) (B:set (R_n R b)):
  measure_measurable (@euclidean_lebesgue_measure R a) A ->
  measure_measurable (@euclidean_lebesgue_measure R b) B ->
  euclidean_lebesgue_measure (a+b) ((@euclidean_block_split R a b) @^-1` (A `*` B))=
    (euclidean_lebesgue_measure a A*euclidean_lebesgue_measure b B)%E.
Proof.
move=>hA hB.
have h:=congr1 (fun rho=>rho (A `*` B)) (@euclidean_block_measure R a b).
change (euclidean_lebesgue_measure (a+b) ((@euclidean_block_split R a b) @^-1` (A `*` B))=product_measure (euclidean_lebesgue_is_measure R a)
  (euclidean_lebesgue_is_measure R b) (A `*` B)) in h.
rewrite h.
exact:(product_measure_rectangle_value (euclidean_lebesgue_is_measure R a)
  (euclidean_lebesgue_is_measure R b) hA hB).
Qed.
