(** Federer (1969), 3.1.6, pp. 216–217: the Fubini
    step from null exceptional sets on coordinate lines to an ambient
    Lebesgue-null exceptional set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanCoordinateLineMap EuclideanBlockCoordinates EuclideanBlockMeasure
  EuclideanEpimorphismMeasurable EuclideanOneCoordinate ScalarEuclideanApproximateLimits
  EuclideanAdditiveGroup EuclideanLebesgueTranslation EuclideanClosedBallVolume EuclideanNoncenteredVitali
  LebesgueScalarMeasure RealMetricBackground MetricClosedBalls
  MeasureUP MeasureBasic MeasurePushforward PushforwardMeasurableSets
  ProductMeasure ProductSections ProductSetFubini ProductNullFubini
  MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUniqueness MeasureConullZeroIntegral
  CountablyMeasurableUP CountablyMeasurableSubsets CountablyMeasurableProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [euclidean_coordinate_incidence_measurable]:
    the measurable coordinate-line set in the Fubini argument of
    Federer 3.1.6, pp. 216–217, also used for the
    restrictions in 3.1.7, p. 217. Joint measurability
    follows from the epimorphism in 3.1.3(3), p. 213. *)
Lemma euclidean_coordinate_incidence_measurable (R : realType) m (i : 'I_m)
    (N : set (inner_metric_space (@euclidean_inner_productP R m))) :
  measure_measurable (@euclidean_lebesgue_measure R m) N ->
  measure_measurable (product_measure (euclidean_lebesgue_is_measure R m)
    (euclidean_lebesgue_is_measure R 1))
    [set p : inner_metric_space (@euclidean_inner_productP R m) *
      inner_metric_space (@euclidean_inner_productP R 1) |
      N (p.1+euclidean_one_project p.2*:(@coordinate_basis R m i))].
Proof.
move=> hN; rewrite -euclidean_block_measure.
apply: pushforward_measurable_from_preimage.
pose p := GRing.Linear.clone _ _ _ _ (@euclidean_coordinate_line_map R m i) _.
change (measure_measurable (@euclidean_lebesgue_measure R (m+1)) (p @^-1` N)).
exact: (euclidean_epimorphism_preimage_measurable
  (@euclidean_coordinate_line_map_surjective R m i) hN).
Qed.

(** Source for [euclidean_coordinate_lines_almost_null]: the use of
    Fubini in Federer 3.1.6, pp. 216–217. We parametrise
    each line by (a,t) -> a+t e_i, as already used in
    3.1.4, p. 214. Null vertical sections and translation
    invariance force the ambient exceptional measure to vanish.
    This avoids an additional coordinate-deletion construction. *)
Theorem euclidean_coordinate_lines_almost_null (R : realType) m (i : 'I_m)
    (N : set (inner_metric_space (@euclidean_inner_productP R m))) :
  measure_measurable (@euclidean_lebesgue_measure R m) N ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R m)
    [set a | lebesgue_scalar_measure
      [set t : real_line_metric R | N (a+t*:(@coordinate_basis R m i))]=0%E] ->
  @euclidean_lebesgue_measure R m N=0%E.
Proof.
move=> hN hlines.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose T := inner_metric_space (@euclidean_inner_productP R 1).
pose hm := euclidean_lebesgue_is_measure R m.
pose ht := euclidean_lebesgue_is_measure R 1.
pose rho := product_measure hm ht.
pose S : set (X*T)%type := [set p | N (p.1+euclidean_one_project p.2*:(@coordinate_basis R m i))].
have hSm : measure_measurable rho S.
  exact (@euclidean_coordinate_incidence_measurable R m i N hN).
have hSc : measure_countably_measurable rho S.
  apply: (measurable_subset_countably_measurable (product_measure_is_measure hm ht)
    hSm (fun _ _=>Logic.I)).
  exact (@product_whole_countably_measurable R [the choiceType of X]
    [the choiceType of T] _ _ hm ht
    (euclidean_lebesgue_countably_measurable R m)
    (euclidean_lebesgue_countably_measurable R 1)).
have hv : measure_almost_everywhere (@euclidean_lebesgue_measure R m)
    [set a | @euclidean_lebesgue_measure R 1 (product_vertical_section S a)=0%E].
  apply: (measure_almost_everywhere_mono hm _ hlines)=> a ha.
  have he : product_vertical_section S a=(@euclidean_one_project R) @^-1`
      [set t : real_line_metric R | N (a+t*:(@coordinate_basis R m i))] by [].
  change (@euclidean_lebesgue_measure R 1 (product_vertical_section S a)=0%E).
  by rewrite he -euclidean_one_project_measure_preimage.
have hS0 : rho S=0%E.
  have hi := (@product_set_fubini R [the choiceType of X] [the choiceType of T]
    _ _ hm ht S hSc).2.2.1.
  apply: (measure_integral_unique hi _).
  apply: (measure_almost_zero_integral hm).
  apply: (measure_almost_everywhere_mono hm _ hv)=> a ha.
  exact ha.
have hh := @product_null_horizontal_sections R [the choiceType of X]
  [the choiceType of T] _ _ hm ht S hS0.
have hsection t : @euclidean_lebesgue_measure R m (product_horizontal_section S t)=
    @euclidean_lebesgue_measure R m N.
  have he : product_horizontal_section S t=
      euclidean_translation (euclidean_one_project t*:(@coordinate_basis R m i)) @^-1` N.
    apply/seteqP; split=> a; by rewrite /S /product_horizontal_section /euclidean_translation /= addrC.
  by rewrite he -/(measure_pushforward _ _ _)
    euclidean_lebesgue_translation_pushforward.
apply: contrapT=> hn.
pose I := metric_closed_ball (0 : T) (1 : R).
have hI : (0<@euclidean_lebesgue_measure R 1 I)%E.
  exact: euclidean_closed_ball_positive (@ltr01 R).
have hI0 : @euclidean_lebesgue_measure R 1 I=0%E.
  apply: (measure_null_subset ht _ hh)=> t _ hz.
  apply: hn; by rewrite -(hsection t).
by rewrite hI0 ltxx in hI.
Qed.

(** Source for [euclidean_coordinate_lines_null]: the all-lines
    special case of the Fubini step in Federer 3.1.6,
    pp. 216–217. Every coordinate curve is Lipschitz there. *)
Corollary euclidean_coordinate_lines_null (R : realType) m (i : 'I_m)
    (N : set (inner_metric_space (@euclidean_inner_productP R m))) :
  measure_measurable (@euclidean_lebesgue_measure R m) N ->
  (forall a : R_n R m, lebesgue_scalar_measure
    [set t : real_line_metric R | N (a+t*:(@coordinate_basis R m i))]=0%E) ->
  @euclidean_lebesgue_measure R m N=0%E.
Proof.
move=> hN hlines; apply: (euclidean_coordinate_lines_almost_null (i:=i) hN).
apply: (measure_almost_everywhere_mono (euclidean_lebesgue_is_measure R m)
  _ (measure_almost_everywhere_true (euclidean_lebesgue_is_measure R m)))=> a _.
exact: hlines.
Qed.
