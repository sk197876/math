(** Federer (1969), 3.1.7, p. 217: the complement of
    a measurable domain has zero density along each coordinate line
    at almost every point of that domain. This expands the use of
    3.1.3(5), p. 213, with an arbitrary chosen coordinate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions EuclideanOneCoordinate
  EuclideanCoordinateNullSections EuclideanSectionDensityMeasurable
  EuclideanApproximateTranslation EuclideanApproximateContext EuclideanClosedBallVolume EuclideanNoncenteredVitali
  ScalarEuclideanApproximateLimits CenteredDensityTransport RealMetricBackground
  LebesgueScalarMeasure PartialFunctionUP MeasureUP MeasureBasic MeasureFiniteClosure
  MeasureAlmostUP MeasureAlmostBasic MeasureSetDensity MeasureDensityPoints
  DensityMeasurableSets CenteredBallRelations MetricClosedBalls
  ProductMeasure ProductSections ProductSetFubini CountablyMeasurableUP
  CountablyMeasurableSubsets CountablyMeasurableProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [coordinate_section_complement_zero_density]:
    the coordinate-section density condition invoked in Federer
    3.1.7, p. 217. The one-dimensional Euclidean factor
    is identified with the scalar increment line below. *)
Definition coordinate_section_complement_zero_density (R : realType) m
    (A : set (R_n R m)) (i : 'I_m) (a : R_n R m) :=
  partial_function_graph
    (measure_set_density (@euclidean_lebesgue_measure R 1)
      (@centered_closed_ball_relation R
        [the metricType R of inner_metric_space (@euclidean_inner_productP R 1)])
      [set t : inner_metric_space (@euclidean_inner_productP R 1) |
        ~A (a+euclidean_one_project t*:(@coordinate_basis R m i))]) 0 0%E.

(** Source for [coordinate_section_density_measurable]: the
    measurable exceptional locus for the application of 3.1.3(5)
    in Federer 3.1.7, p. 217. This is the exact
    density-zero predicate, by 3.1.3(1)–(2), pp. 212–213. *)
Lemma coordinate_section_density_measurable (R : realType) m
    (A : set (inner_metric_space (@euclidean_inner_productP R m))) (i : 'I_m) :
  measure_measurable (@euclidean_lebesgue_measure R m) A ->
  measure_measurable (@euclidean_lebesgue_measure R m)
    (coordinate_section_complement_zero_density A i).
Proof.
move=> hA.
have hS := @euclidean_coordinate_incidence_measurable R m i (~` A)
  (measure_measurable_complement hA).
exact (@euclidean_zero_density_section_measurable R m 1 _ hS).
Qed.

(** Source for [coordinate_section_density_almost_everywhere]:
    the use of 3.1.3(5) in Federer 3.1.7, p. 217.
    Fubini first gives measurable sections; 2.9.11 on each
    section gives density-one points; Fubini then gives the
    ambient almost-everywhere assertion. *)
Theorem coordinate_section_density_almost_everywhere (R : realType) m
    (A : set (inner_metric_space (@euclidean_inner_productP R m))) (i : 'I_m) :
  measure_measurable (@euclidean_lebesgue_measure R m) A ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m) A
    (coordinate_section_complement_zero_density A i).
Proof.
move=> hA.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose T := inner_metric_space (@euclidean_inner_productP R 1).
pose hm := euclidean_lebesgue_is_measure R m.
pose ht := euclidean_lebesgue_is_measure R 1.
pose S : set (X*T)%type := [set p |
  A (p.1+euclidean_one_project p.2*:(@coordinate_basis R m i))].
have hSm : measure_measurable (product_measure hm ht) S.
  exact (@euclidean_coordinate_incidence_measurable R m i A hA).
have hSc : measure_countably_measurable (product_measure hm ht) S.
  apply: (measurable_subset_countably_measurable (product_measure_is_measure hm ht)
    hSm (fun _ _=>Logic.I)).
  exact (@product_whole_countably_measurable R [the choiceType of X]
    [the choiceType of T] _ _ hm ht
    (euclidean_lebesgue_countably_measurable R m)
    (euclidean_lebesgue_countably_measurable R 1)).
have hsections := (@product_set_fubini R [the choiceType of X] [the choiceType of T]
  _ _ hm ht S hSc).1.
pose G := coordinate_section_complement_zero_density A i.
have hGm : measure_measurable (@euclidean_lebesgue_measure R m) G.
  exact (@coordinate_section_density_measurable R m A i hA).
have hNm : measure_measurable (@euclidean_lebesgue_measure R m) (A `\` G).
  exact (@measure_measurable_difference R [the choiceType of X]
    (@euclidean_lebesgue_measure R m) hm A G hA hGm).
apply: (euclidean_coordinate_lines_almost_null (i:=i) hNm).
apply: (measure_almost_everywhere_mono hm _ hsections)=> a hsection.
pose At := product_vertical_section S a.
have hD := density_complement_zero_points_conclusions At (euclidean_approximate_context R 1).
have hnull : @euclidean_lebesgue_measure R 1
    (At `\` measure_density_complement_zero_points
      (@euclidean_lebesgue_measure R 1)
      (@centered_closed_ball_relation R [the metricType R of T]) At)=0%E.
  exact: hD.2.2.2.1 hsection.
change (@lebesgue_scalar_measure R
  [set t : real_line_metric R | (A `\` G) (a+t*:(@coordinate_basis R m i))]=0%E).
rewrite euclidean_one_project_measure_preimage.
apply: (measure_null_subset ht _ hnull)=> z [hzA hzG]; split=> // hzD.
apply: hzG.
have hsource : partial_function_graph
    (measure_set_density (@euclidean_lebesgue_measure R 1)
      (@centered_closed_ball_relation R [the metricType R of T]) (~` At)) (z+0) 0%E.
  by rewrite addr0.
have hh := @euclidean_zero_density_translation R 1 z 0 (~` At) hsource.
have he : (fun t : T=>z+t) @^-1` (~` At)=
    [set t : T | ~A ((a+euclidean_one_project z*:(@coordinate_basis R m i))+
      euclidean_one_project t*:(@coordinate_basis R m i))].
  apply/seteqP; split=> t;
    by rewrite /At /S /product_vertical_section /= /euclidean_one_project ffunE scalerDl addrA.
by rewrite he in hh.
Qed.

(** Source for [coordinate_section_density_scalar]: scalar-coordinate
    interpretation of the domain-density condition in Federer 3.1.7,
    p. 217, for the quotient in 3.1.2, p. 212.
    The existing isometry preserves actual outer measures. *)
Lemma coordinate_section_density_scalar (R : realType) m
    (A : set (R_n R m)) (i : 'I_m) (a : R_n R m) :
  coordinate_section_complement_zero_density A i a ->
  partial_function_graph
    (@measure_set_density R [the metricType R of real_line_metric R]
      (@lebesgue_scalar_measure R)
      (@centered_closed_ball_relation R [the metricType R of real_line_metric R])
      [set t : real_line_metric R | ~A (a+t*:(@coordinate_basis R m i))]) 0 0%E.
Proof.
move=> hD.
pose T := inner_metric_space (@euclidean_inner_productP R 1).
pose N : set T := [set t | ~A (a+euclidean_one_project t*:(@coordinate_basis R m i))].
have hballs (x : T) r (hr : 0<r) :
    (0<@euclidean_lebesgue_measure R 1 (metric_closed_ball x r))%E /\
    @euclidean_lebesgue_measure R 1 (metric_closed_ball x r) \is a fin_num.
  split; first exact: euclidean_closed_ball_positive.
  by rewrite (euclidean_closed_ball_normalized_volume x (ltW hr)) fin_numE.
have h0 : euclidean_one_embed (0 : R)=0.
  by apply/ffunP=> j; rewrite /euclidean_one_embed !ffunE.
have hbase : partial_function_graph
    (measure_set_density (@euclidean_lebesgue_measure R 1)
      (@centered_closed_ball_relation R [the metricType R of T]) N)
      (euclidean_one_embed 0) 0%E by rewrite h0.
have hh := @centered_zero_density_isometric_preimage R
  [the metricType R of real_line_metric R] [the metricType R of T]
  (@lebesgue_scalar_measure R) (@euclidean_lebesgue_measure R 1)
  (@euclidean_one_embed R) N 0 (lebesgue_scalar_is_measure R)
  (euclidean_lebesgue_is_measure R 1) (@scalar_centered_ball_positive_finite R)
  hballs (@euclidean_one_embed_isometry R) (@euclidean_one_embed_measure_preimage R) hbase.
have he : (@euclidean_one_embed R) @^-1` N=
    [set t : real_line_metric R | ~A (a+t*:(@coordinate_basis R m i))].
  apply/seteqP; split=> t; by rewrite /N /= euclidean_one_embedK.
by rewrite he in hh.
Qed.
