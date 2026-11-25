(** Federer (1969), 3.1.3(1)–(2), pp. 212–213: the locus of parameters
    whose exceptional section has density zero is measurable. The
    countable epsilon/delta formulation expands the application of (1)
    to the strict level sets in (2). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanBallVolume EuclideanClosedBallVolume EuclideanNoncenteredVitali
  MetricClosedBalls MeasureUP MeasureBasic MeasureCountableClosure ProductMeasure
  ProductSections PartialFunctionUP MeasureSetDensity CenteredBallRelations
  EuclideanZeroDensitySmallMass CenteredZeroDensityCriterion ExtendedRealReciprocalBounds
  EuclideanSectionMassMeasurable.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_zero_density_countable_ball_bounds]: supporting
    countable version of the density-zero condition used in Federer
    3.1.3(2), p. 213. Every precision and cutoff is chosen from the
    positive reciprocals of natural numbers. The set need not be measurable. *)
Lemma euclidean_zero_density_countable_ball_bounds (R : realType) k
    (A : set (inner_metric_space (@euclidean_inner_productP R k))) a :
  partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R k)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R k)]) A) a 0 <->
  forall i : nat, exists j : nat, forall r : R,
    (0<r)%R -> (r<(j.+1%:R)^-1)%R ->
    euclidean_lebesgue_measure k (A `&` metric_closed_ball a r)<=
      ((i.+1%:R)^-1*euclidean_unit_ball_volume R k*r^+k)%R%:E.
Proof.
split.
- move=> hA i.
  have hi : (0<(i.+1%:R : R)^-1)%R by rewrite invr_gt0 ltr0n.
  have [d [hd hs]] := euclidean_zero_density_small_mass hA hi.
  have [j hj] := positive_reciprocal_nat_small hd.
  exists j=> r hr hrj.
  have hh := ltW (hs r hr (lt_trans hrj hj)).
  by rewrite (euclidean_closed_ball_normalized_volume a (ltW hr)) -EFinM mulrA in hh.
- move=> hcount.
  apply: (centered_small_mass_zero_density (euclidean_lebesgue_is_measure R k)).
  + move=> x r hr; split; first exact: euclidean_closed_ball_positive.
    by rewrite (euclidean_closed_ball_normalized_volume x (ltW hr)) fin_numE.
  + move=> c hc; have [i hi] := positive_reciprocal_nat_small hc.
    have [j hj] := hcount i.
    exists ((j.+1%:R)^-1)%R; split; first by rewrite invr_gt0 ltr0n.
    move=> r hr hrj; apply: le_lt_trans (hj r hr hrj) _.
    rewrite (euclidean_closed_ball_normalized_volume a (ltW hr)) -EFinM lte_fin -mulrA.
    have hp : (0<euclidean_unit_ball_volume R k*r^+k)%R.
      rewrite mulr_gt0 ?exprn_gt0 //.
      exact: (euclidean_unit_ball_volumeE R k).2.
    by rewrite (ltr_pM2r hp).
Qed.

(** Source for [euclidean_zero_density_section_measurable]: the
    measurability step applying (1) to exceptional sets in Federer
    3.1.3(2), p. 213. This is the density-zero predicate at the section
    origin, not an almost-everywhere replacement of that predicate. *)
Theorem euclidean_zero_density_section_measurable (R : realType) m k
    (S : set (inner_metric_space (@euclidean_inner_productP R m) *
      inner_metric_space (@euclidean_inner_productP R k))) :
  measure_measurable (product_measure (euclidean_lebesgue_is_measure R m)
    (euclidean_lebesgue_is_measure R k)) S ->
  measure_measurable (@euclidean_lebesgue_measure R m)
    [set x | partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R k)
      (@centered_closed_ball_relation R
        [the metricType R of inner_metric_space (@euclidean_inner_productP R k)])
      (product_vertical_section S x)) (0%R : R_n R k) 0].
Proof.
move=> hS.
have he : [set x | partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R k)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R k)])
    (product_vertical_section S x)) (0%R : R_n R k) 0]=
  \bigcap_(i in @setT nat) \bigcup_(j in @setT nat)
    [set x | forall r : R, (0<r)%R -> (r<(j.+1%:R)^-1)%R ->
      euclidean_lebesgue_measure k (product_vertical_section S x `&` metric_closed_ball ((0%R : R_n R k) : inner_metric_space (@euclidean_inner_productP R k)) r)
        <= ((i.+1%:R)^-1*euclidean_unit_ball_volume R k*r^+k)%R%:E].
  apply/seteqP; split=> x hx.
  - move=> i _; have [j hj] := (euclidean_zero_density_countable_ball_bounds _ _).1 hx i.
    by exists j.
  - apply: (euclidean_zero_density_countable_ball_bounds _ _).2=> i.
    have [j _ hj] := hx i Logic.I; by exists j.
rewrite he; apply: (measure_measurable_countable_intersection (euclidean_lebesgue_is_measure R m));
  first exact: countableP.
move=> i _; apply: (measure_measurable_countable_union (euclidean_lebesgue_is_measure R m));
  first exact: countableP.
move=> j _; exact: euclidean_small_section_mass_measurable hS.
Qed.
