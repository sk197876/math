(** Coordinate rearrangement for Federer (1969), 2.10.16, p. 178.
    Interchange the two normal offsets with the two frame parameters, then
    use the actual Euclidean block isomorphism of 2.6.5, p. 120. Its measure
    identity includes empty coordinate blocks. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanProjectionSpace EuclideanProjectionMetric EuclideanBlockCoordinates EuclideanBlockMeasure
  EuclideanLebesgueDimensions EuclideanLebesgueHaar ProductMeasure ProductMeasureBijections ProductMeasureShuffle
  MeasureUP MeasureBijectionUP MeasureBijectionLaws MeasurePushforward CountablyMeasurableUP
  StackedNormalFamily MappingMultiplicity CountingMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_block_measure_bijection]: supporting
    abstract coordinate-change package for 2.10.16,
    p. 178, from the direct Lebesgue block identity
    of 2.6.5, p. 120, including empty blocks. *)
Lemma euclidean_block_measure_bijection (R : realType) (a r : nat) :
  is_measure_bijection (@euclidean_lebesgue_measure R (a+r))
    (product_measure (@euclidean_lebesgue_is_measure R a) (@euclidean_lebesgue_is_measure R r))
    (@euclidean_block_split R a r) (@euclidean_block_join R a r).
Proof. constructor; [exact: euclidean_block_splitK|exact: euclidean_block_joinK|exact: euclidean_block_measure]. Qed.

(** Source for [stacked_normal_slice_parameter_bijection]:
    supporting actual product-coordinate exchange for
    2.10.16, p. 178: two independent offset/frame
    pairs become their joined offset and frame pair. *)
Lemma stacked_normal_slice_parameter_bijection (R : realType) (a r : nat)
    (G : choiceType) (theta : set G -> \bar R) (ht : is_measure theta) :
  measure_countably_measurable theta setT ->
  is_measure_bijection
    (product_measure (product_measure_is_measure (@euclidean_lebesgue_is_measure R a) ht)
      (product_measure_is_measure (@euclidean_lebesgue_is_measure R r) ht))
    (product_measure (@euclidean_lebesgue_is_measure R (a+r)) (product_measure_is_measure ht ht))
    (fun z => (euclidean_block_join (z.1.1,z.2.1),(z.1.2,z.2.2)))
    (fun z => (((euclidean_block_split z.1).1,z.2.1),((euclidean_block_split z.1).2,z.2.2))).
Proof.
move=> hw.
have h1 := @countable_product_four_shuffle R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R a)] G
  [the choiceType of inner_metric_space (@euclidean_inner_productP R r)] G
  (@euclidean_lebesgue_measure R a) theta (@euclidean_lebesgue_measure R r) theta
  (@euclidean_lebesgue_is_measure R a) ht (@euclidean_lebesgue_is_measure R r) ht
  (euclidean_lebesgue_countably_measurable R a) hw (euclidean_lebesgue_countably_measurable R r) hw.
have h2 := measure_bijection_product
  (product_measure_is_measure (@euclidean_lebesgue_is_measure R a) (@euclidean_lebesgue_is_measure R r))
  (product_measure_is_measure ht ht) (@euclidean_lebesgue_is_measure R (a+r))
  (product_measure_is_measure ht ht) (measure_bijection_inverse (euclidean_block_measure_bijection R a r))
  (measure_bijection_identity (product_measure ht ht)).
exact (measure_bijection_compose h1 h2).
Qed.

(** Source for [stacked_normal_slice_multiplicity]: supporting
    point-set double-count identity for 2.10.16,
    p. 178. Stacking p and q at the joined offset
    counts exactly the q fibre inside the p slice.
    No finiteness, measurability, or generic rank is assumed. *)
Lemma stacked_normal_slice_multiplicity (R : realType) (n a r : nat)
    (F : orthogonal_projection_metric_space R n a * orthogonal_projection_metric_space R n r ->
      {linear R_n R n -> R_n R (a+r)}) :
  is_stacked_normal_family F -> forall p q A y z,
  @mapping_multiplicity R [the choiceType of (R_n R n : Type)] [the choiceType of (R_n R (a+r) : Type)]
    (F (p,q)) A (euclidean_block_join (y,z))=
  @mapping_multiplicity R [the choiceType of (R_n R n : Type)] [the choiceType of (R_n R r : Type)]
    (euclidean_projection_linear q) (A `&` [set x | euclidean_projection_linear p x=y]) z.
Proof.
move=> hF p q A y z.
rewrite /mapping_multiplicity /mapping_fibre.
congr (counting_measure _); apply/seteqP; split=> x.
- move=> [hx he].
  have hh := congr1 (@euclidean_block_split R a r) he.
  rewrite (hF p q x) euclidean_block_joinK in hh.
  have h1 := congr1 (@fst (R_n R a) (R_n R r)) hh.
  have h2 := congr1 (@snd (R_n R a) (R_n R r)) hh.
  by split; first split.
- move=> [[hx hy] hz]; split=> //.
  by rewrite (stacked_normal_familyE hF p q x) hy hz.
Qed.
