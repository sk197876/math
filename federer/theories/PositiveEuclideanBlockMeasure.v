(** Federer (1969), 2.6.5, p. 120: the usual isomorphism R^(m+n) to R^m
    times R^n maps Lebesgue measure to the product measure. This file proves
    the assertion for positive block dimensions using the already proved
    finite-association theorem and the actual ordered Euclidean coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasurePushforward ProductMeasure ProductMeasureBijections
  CountableMeasureSpaceUP MeasureBijectionUP MeasureBijectionLaws MeasureBijectionCoordinateTransport
  MeasureAssociationTrees MeasureTreeCoordinateInjectivity LebesgueMeasureTree LebesgueTreeIdentification
  EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates EuclideanCoordinateLists
  EuclideanLebesgue EuclideanLebesgueDimensions EuclideanLebesgueBijections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section PositiveBlocks.
Variable R : realType.
Variables m n : nat.
Local Notation E k := (inner_metric_space (@euclidean_inner_productP R k)).
Local Notation T k := (@lebesgue_measure_tree R k).

(** Source for [positive_block_dimension]: supporting
    dimension-index equality for the usual identification
    in Federer 2.6.5, p. 120. *)
Lemma positive_block_dimension : (m+n).+2 = m.+1+n.+1.
Proof. by rewrite addSn addnS. Qed.

(** Source for [positive_block_tree_map]: supporting actual
    Euclidean block map expressed in scalar factor trees,
    Federer 2.6.5, p. 120. Tail-first factor enumeration
    reverses both blocks and their order. *)
Definition positive_block_tree_map (x : countable_measure_carrier (measure_tree_space (T (m+n).+1))) :=
  let y := euclidean_dimension_cast positive_block_dimension (lebesgue_tree_decode (m+n).+1 x) in
  let p := @euclidean_block_split R m.+1 n.+1 y in
  (lebesgue_tree_encode n p.2, lebesgue_tree_encode m p.1).

(** Source for [positive_block_tree_factors]: supporting
    equality of the scalar factor lists for the block map
    in Federer 2.6.5, pp. 119–120. *)
Lemma positive_block_tree_factors :
  measure_tree_factors (T (m+n).+1) = measure_tree_factors (MeasurePair (T n) (T m)).
Proof.
change (measure_tree_factors (T (m+n).+1) = measure_tree_factors (T n) ++ measure_tree_factors (T m)).
by rewrite !lebesgue_tree_factors -nseqD addSn addnS [n+m]addnC.
Qed.

(** Source for [positive_block_tree_coordinates]: supporting
    preservation of every ordered scalar coordinate by the
    usual block isomorphism in Federer 2.6.5, p. 120. *)
Lemma positive_block_tree_coordinates x :
  measure_tree_coordinates (MeasurePair (T n) (T m)) (positive_block_tree_map x) =
    measure_tree_coordinates (T (m+n).+1) x.
Proof.
rewrite /positive_block_tree_map.
change (measure_tree_coordinates (T n)
    (lebesgue_tree_encode n (@euclidean_block_split R m.+1 n.+1
      (euclidean_dimension_cast positive_block_dimension (lebesgue_tree_decode (m+n).+1 x))).2) ++
  measure_tree_coordinates (T m)
    (lebesgue_tree_encode m (@euclidean_block_split R m.+1 n.+1
      (euclidean_dimension_cast positive_block_dimension (lebesgue_tree_decode (m+n).+1 x))).1) =
  measure_tree_coordinates (T (m+n).+1) x).
rewrite !lebesgue_tree_encode_coordinates lebesgue_tree_decode_coordinates -map_cat -rev_cat.
congr (map _ (rev _)).
by rewrite -euclidean_block_split_list euclidean_dimension_cast_list.
Qed.

(** Source for [positive_block_tree_image]: supporting
    finite-association measure identity for the actual block
    coordinates, Federer 2.6.5, p. 120. *)
Lemma positive_block_tree_image :
  measure_pushforward positive_block_tree_map (countable_measure_value (measure_tree_space (T (m+n).+1))) =
    countable_measure_value (measure_tree_space (MeasurePair (T n) (T m))).
Proof.
exact (@finite_product_coordinate_map_image R (T (m+n).+1) (MeasurePair (T n) (T m))
  positive_block_tree_map positive_block_tree_factors positive_block_tree_coordinates).
Qed.

(** Source for [positive_euclidean_block_measure]: direct
    block identity in Federer 2.6.5, p. 120, for
    positive m and n. Both sides are the already sealed
    Euclidean measures, and the map is the usual first-block,
    last-block coordinate split. *)
Theorem positive_euclidean_block_measure :
  measure_pushforward (@euclidean_block_split R m.+1 n.+1)
    (@euclidean_lebesgue_measure R (m.+1+n.+1)) =
  product_measure (euclidean_lebesgue_is_measure R m.+1) (euclidean_lebesgue_is_measure R n.+1).
Proof.
have hs := measure_bijection_compose
  (@euclidean_dimension_cast_bijection R _ _ (esym positive_block_dimension))
  (lebesgue_tree_identification R (m+n).+1).
have hp := @measure_bijection_product R _ _ _ _ _ _ _ _
  (euclidean_lebesgue_is_measure R n.+1) (euclidean_lebesgue_is_measure R m.+1)
  (countable_measure_law (measure_tree_space (T n))) (countable_measure_law (measure_tree_space (T m)))
  (lebesgue_tree_encode n) (lebesgue_tree_decode n) (lebesgue_tree_encode m) (lebesgue_tree_decode m)
  (lebesgue_tree_identification R n) (lebesgue_tree_identification R m).
have ht := measure_bijection_compose
  (measure_bijection_swap (euclidean_lebesgue_is_measure R m.+1) (euclidean_lebesgue_is_measure R n.+1)) hp.
apply: (measure_bijection_image_transport hs ht positive_block_tree_image)=> x.
rewrite /positive_block_tree_map lebesgue_tree_encodeK.
have hc : euclidean_dimension_cast positive_block_dimension
    (euclidean_dimension_cast (esym positive_block_dimension) x) = x.
  have hh : esym (esym positive_block_dimension) = positive_block_dimension := Prop_irrelevance _ _.
  have hi := euclidean_dimension_castK (esym positive_block_dimension) x.
  by rewrite hh in hi.
by rewrite hc.
Qed.
End PositiveBlocks.
