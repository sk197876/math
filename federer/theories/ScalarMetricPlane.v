(** Auxiliary scalar coordinates for Federer (1969),
    2.8.20, p. 152. The maximum product metric
    retains the usual topology of the plane. Its closed
    balls are squares of area 4r^2, which permits applying
    2.8.7 to finite fan unions. The eventual counterexample
    is transported to the book's Euclidean plane. This is
    supporting coordinate infrastructure; source titles and
    the proof-route departure: QuadraticDiameterAdequacy.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology ring lra.
From Federer Require Import RealMetricBackground MetricProductBackground TopologicalProductMaps
  ScalarPlaneRectangles MeasureUP MeasureBasic MetricClosedBalls MetricDiameterUP MetricDiameter
  CoveringFamilyUP BorelRegularMeasureUP ProductBorelRegularity LebesgueScalarMeasure
  StieltjesBorelRegularity IntervalBumpFunctions ProductMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [scalar_metric_plane]: auxiliary maximum metric
    for the coordinate proof of Federer 2.8.20, p. 152.
    It is the established metric product of the two real lines. *)
Definition scalar_metric_plane (R : realType) : metricType R :=
  [the metricType R of metric_product [the metricType R of real_line_metric R]
    [the metricType R of real_line_metric R]].

(** Source for [scalar_metric_plane_ball]: supporting square
    description of a closed ball for the application of
    Federer 2.8.7 in the proof of 2.8.20, p. 152. *)
Lemma scalar_metric_plane_ball (R : realType) (a : scalar_metric_plane R) (r : R) :
  metric_closed_ball a r = scalar_closed_rectangle (a.1-r)%R (a.1+r)%R (a.2-r)%R (a.2+r)%R.
Proof.
apply/seteqP; split; move=> [x y] hx.
- move: hx; rewrite /metric_closed_ball /= metric_product_distanceE
    !real_line_metric_distanceE /= ge_max !ler_norml => /andP [/andP [hx1 hx2] /andP [hy1 hy2]].
  rewrite /scalar_closed_rectangle /= !in_itv /=; split; apply/andP; split; lra.
- move: hx; rewrite /scalar_closed_rectangle /= !in_itv /=.
  move=> [/andP [hx1 hx2] /andP [hy1 hy2]].
  rewrite /metric_closed_ball /= metric_product_distanceE !real_line_metric_distanceE /=
    ge_max !ler_norml; apply/andP; split; apply/andP; split; lra.
Qed.

(** Source for [scalar_metric_plane_ball_area]: supporting
    quadratic ball-area bound for Federer 2.8.20, p. 152.
    It is an equality, including radius zero, in this auxiliary metric. *)
Lemma scalar_metric_plane_ball_area (R : realType) (a : scalar_metric_plane R) (r : R) :
  (0<=r)%R -> scalar_plane_lebesgue (metric_closed_ball a r) = (4*r*r)%:E.
Proof.
move=> hr.
have h1 : (a.1-r<=a.1+r)%R by lra.
have h2 : (a.2-r<=a.2+r)%R by lra.
rewrite scalar_metric_plane_ball (scalar_closed_rectangle_value h1 h2).
congr (_%:E); ring.
Qed.

(** Source for [scalar_plane_rectangle_closed]: closedness
    of the compact eligible rectangles in Federer 2.8.20,
    p. 152, in the unchanged coordinate product topology. *)
Lemma scalar_plane_rectangle_closed (R : realType) (a b c d : R) :
  closed (scalar_closed_rectangle a b c d : set (scalar_metric_plane R)).
Proof.
have he : scalar_closed_rectangle a b c d =
    (@fst R R) @^-1` `[a,b] `&` (@snd R R) @^-1` `[c,d] by [].
rewrite he; apply: closedI.
- apply: preimage_closed; last exact: segment_closed_real.
  by move=> x _; exact: first_projection_continuous.
- apply: preimage_closed; last exact: segment_closed_real.
  by move=> x _; exact: second_projection_continuous.
Qed.

(** Source for [scalar_plane_borel_regular]: established
    product Borel regularity supporting the standing hypotheses
    of Federer 2.8.1, p. 141, in the coordinate
    proof of 2.8.20, p. 152. *)
Lemma scalar_plane_borel_regular (R : realType) :
  is_borel_regular_measure (@scalar_plane_lebesgue R : set (scalar_metric_plane R) -> \bar R).
Proof.
have [U hU] := @real_line_countable_open_base_exists R.
exact (@product_measure_borel_regular R R^o R^o
  (@lebesgue_scalar_measure R) (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) (lebesgue_scalar_is_measure R) U U hU hU
  (lebesgue_scalar_borel_regular R) (lebesgue_scalar_borel_regular R)).
Qed.

(** Source for [scalar_plane_bounded_finite]: bounded sets
    have finite area, the standing hypothesis of Federer
    2.8.1, p. 141, supporting 2.8.20, p. 152.
    A bounded nonempty set lies in a finite-area square;
    the empty set is treated without selecting a point. *)
Lemma scalar_plane_bounded_finite (R : realType) (A : set (scalar_metric_plane R)) :
  metric_set_bounded A -> scalar_plane_lebesgue A < +oo.
Proof.
move=> hb; have [->|/set0P [a ha]] := eqVneq A set0.
- by rewrite (measure_empty (scalar_plane_lebesgue_is_measure R)) ltry.
- pose D := extended_metric_diameter A.
  have hD := extended_metric_diameter_specification A.
  have hfin : D \is a fin_num by rewrite (ge0_fin_numE (metric_diameter_nonnegative hD)).
  pose d := fine D.
  have he : D=d%:E by rewrite /d fineK.
  have hd : (0<=d)%R.
    have hn : 0<=D := metric_diameter_nonnegative hD.
    by move: hn; rewrite he lee_fin.
  have hsub : A `<=` metric_closed_ball a d.
    move=> x hx; have hh : (mdist a x)%:E<=D := metric_diameter_upper hD ha hx.
    by rewrite he lee_fin in hh.
  apply: le_lt_trans (@measure_mono R (scalar_metric_plane R) _
    (scalar_plane_lebesgue_is_measure R) _ _ hsub) _.
  by rewrite scalar_metric_plane_ball_area // ltry.
Qed.

(** Source for [scalar_plane_covering_context]: the original
    standing hypotheses of Federer 2.8.1, p. 141,
    for any closed family used in the counterexample 2.8.20,
    p. 152. No family regularity is assumed beyond closedness. *)
Lemma scalar_plane_covering_context (R : realType)
    (F : set (set (scalar_metric_plane R))) :
  (forall S, F S -> closed S) -> is_covering_theory_context F (@scalar_plane_lebesgue R).
Proof.
move=> hF; constructor.
- exact: scalar_plane_lebesgue_is_measure.
- exact hF.
- exact: borel_regular_open_measurable (scalar_plane_borel_regular R).
- exact: scalar_plane_bounded_finite.
Qed.

(** Source for [scalar_square_pair_distance]: supporting
    diameter estimate for fan unions in a square, needed
    for the application of Federer 2.8.7 to 2.8.20,
    p. 152. The maximum metric gives the side length as bound. *)
Lemma scalar_square_pair_distance (R : realType) (a c s : R)
    (x y : scalar_metric_plane R) :
  scalar_closed_rectangle a (a+s)%R c (c+s)%R x ->
  scalar_closed_rectangle a (a+s)%R c (c+s)%R y -> (mdist x y<=s)%R.
Proof.
rewrite /scalar_closed_rectangle /= !in_itv /=.
move=> [/andP [hx1 hx2] /andP [hx3 hx4]] [/andP [hy1 hy2] /andP [hy3 hy4]].
rewrite metric_product_distanceE !real_line_metric_distanceE /= ge_max !ler_norml.
apply/andP; split; apply/andP; split; lra.
Qed.

(** Source for [scalar_square_subset_diameter]: supporting
    finite diameter of a fan union for Federer 2.8.20,
    p. 152. The bound is derived from the abstract
    diameter laws, including the empty-set convention. *)
Lemma scalar_square_subset_diameter (R : realType) (a c s : R)
    (S : set (scalar_metric_plane R)) :
  (0<=s)%R -> S `<=` scalar_closed_rectangle a (a+s)%R c (c+s)%R ->
  extended_metric_diameter S <= s%:E.
Proof.
move=> hs hS; apply: (metric_diameter_least (extended_metric_diameter_specification S)).
- by rewrite lee_fin.
- move=> x y hx hy; rewrite lee_fin; exact: scalar_square_pair_distance (hS x hx) (hS y hy).
Qed.
