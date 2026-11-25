(** Federer (1969), 2.6.5, p. 120: usual block
    isomorphism and its Lebesgue image measure, with an
    explicit extension to empty coordinate blocks. The positive
    case is exactly the printed assertion; the zero-dimensional
    convention uses unit mass at the sole vector. Source
    editions: PositiveEuclideanBlockMeasure.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FiniteCoordinates EuclideanInnerProduct InnerMetric
  MeasureUP MeasurePushforward ProductMeasure PointMassMeasure BorelRegularMeasureUP
  MeasureBijectionUP MeasureBijectionLaws MeasureBijectionCoordinateTransport SingletonProductMeasure
  EuclideanCoordinateLists EuclideanBlockCoordinates EuclideanLebesgueDimensions
  EuclideanLebesgueBijections PositiveEuclideanBlockMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_block_left_empty]: supporting
    actual coordinate map for an empty first block in the
    zero-dimensional extension of Federer 2.6.5, p. 120. *)
Lemma euclidean_block_left_empty (R : realType) n
    (x : inner_metric_space (@euclidean_inner_productP R (0+n))) :
  @euclidean_block_split R 0 n x = (0,euclidean_dimension_cast (add0n n) x).
Proof.
rewrite (surjective_pairing (@euclidean_block_split R 0 n x)); congr (_, _); first exact: coordinate_zero.
apply: euclidean_coordinate_list_injective.
rewrite euclidean_dimension_cast_list.
have h := @euclidean_block_split_list R 0 n x.
by rewrite /= in h; exact: esym h.
Qed.

(** Source for [euclidean_block_right_empty]: supporting
    actual coordinate map for an empty final block in the
    zero-dimensional extension of Federer 2.6.5, p. 120. *)
Lemma euclidean_block_right_empty (R : realType) n
    (x : inner_metric_space (@euclidean_inner_productP R (n+0))) :
  @euclidean_block_split R n 0 x = (euclidean_dimension_cast (addn0 n) x,0).
Proof.
rewrite (surjective_pairing (@euclidean_block_split R n 0 x)); congr (_, _); last exact: coordinate_zero.
apply: euclidean_coordinate_list_injective.
rewrite euclidean_dimension_cast_list.
have h := @euclidean_block_split_list R n 0 x.
by rewrite /= cats0 in h; exact: esym h.
Qed.

(** Source for [euclidean_block_left_empty_measure]: supporting
    image-measure identity with an empty first block for the
    zero-dimensional extension of Federer 2.6.5, p. 120. *)
Lemma euclidean_block_left_empty_measure (R : realType) n :
  measure_pushforward (@euclidean_block_split R 0 n) (@euclidean_lebesgue_measure R (0+n)) =
    product_measure (euclidean_lebesgue_is_measure R 0) (euclidean_lebesgue_is_measure R n).
Proof.
have hr := borel_regular_is_regular (euclidean_lebesgue_is_measure R n) (euclidean_lebesgue_borel_regular R n).
have hu := @singleton_product_bijection R
  (inner_metric_space (@euclidean_inner_productP R 0))
  (inner_metric_space (@euclidean_inner_productP R n)) 0 _
  (euclidean_lebesgue_is_measure R n) (@coordinate_zero R) hr.
have hp : euclidean_lebesgue_is_measure R 0 =
    @point_mass_is_measure R (inner_metric_space (@euclidean_inner_productP R 0)) 0 := Prop_irrelevance _ _.
rewrite -hp in hu.
have h := measure_bijection_pushforward
  (measure_bijection_compose (@euclidean_dimension_cast_bijection R _ _ (add0n n)) hu).
have he : @euclidean_block_split R 0 n = (fun x => (0,euclidean_dimension_cast (add0n n) x)).
  apply: funext=> x; exact: euclidean_block_left_empty.
rewrite he; exact h.
Qed.

(** Source for [euclidean_block_right_empty_measure]: supporting
    image-measure identity with an empty final block for the
    zero-dimensional extension of Federer 2.6.5, p. 120. *)
Lemma euclidean_block_right_empty_measure (R : realType) n :
  measure_pushforward (@euclidean_block_split R n 0) (@euclidean_lebesgue_measure R (n+0)) =
    product_measure (euclidean_lebesgue_is_measure R n) (euclidean_lebesgue_is_measure R 0).
Proof.
have hr := borel_regular_is_regular (euclidean_lebesgue_is_measure R n) (euclidean_lebesgue_borel_regular R n).
have hu := @singleton_product_bijection R
  (inner_metric_space (@euclidean_inner_productP R 0))
  (inner_metric_space (@euclidean_inner_productP R n)) 0 _
  (euclidean_lebesgue_is_measure R n) (@coordinate_zero R) hr.
have hp : euclidean_lebesgue_is_measure R 0 =
    @point_mass_is_measure R (inner_metric_space (@euclidean_inner_productP R 0)) 0 := Prop_irrelevance _ _.
rewrite -hp in hu.
have hs := measure_bijection_compose hu
  (measure_bijection_swap (euclidean_lebesgue_is_measure R 0) (euclidean_lebesgue_is_measure R n)).
have h := measure_bijection_pushforward
  (measure_bijection_compose (@euclidean_dimension_cast_bijection R _ _ (addn0 n)) hs).
have he : @euclidean_block_split R n 0 = (fun x => (euclidean_dimension_cast (addn0 n) x,0)).
  apply: funext=> x; exact: euclidean_block_right_empty.
rewrite he; exact h.
Qed.

(** Source for [euclidean_block_measure]: direct usual
    isomorphism assertion of Federer 2.6.5, p. 120:
    its image of L^(m+n) equals L^m times L^n. Positive
    dimensions follow finite associativity; empty blocks follow
    the explicitly documented unit-mass convention. *)
Theorem euclidean_block_measure (R : realType) m n :
  measure_pushforward (@euclidean_block_split R m n) (@euclidean_lebesgue_measure R (m+n)) =
    product_measure (euclidean_lebesgue_is_measure R m) (euclidean_lebesgue_is_measure R n).
Proof.
case: m=> [|m]; first exact: euclidean_block_left_empty_measure.
case: n=> [|n]; first exact: euclidean_block_right_empty_measure.
exact: positive_euclidean_block_measure.
Qed.
