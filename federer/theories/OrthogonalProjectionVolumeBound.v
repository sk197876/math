(** Federer (1969), 2.10.46, p. 203: outer-volume estimate for an orthogonal
    projection. To make the printed Fubini argument valid for arbitrary
    sets, intersect the source closure with the inverse image of an
    equal-measure Borel hull of its projection. This contains the source,
    has no greater diameter, and has a measurable projected support. Fubini
    and the isodiametric inequality apply without assuming the source or its
    projection measurable. This supporting regularisation uses 2.2.3, pp.
    61–62, and is not separately printed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  CoordinateProjection EuclideanProjectionSpace OrthogonalProjectionChart
  ProjectionSectionVolumeBound EuclideanLebesgueDimensions MeasureUP MeasureBasic
  BorelRegularMeasureUP TopologicalBorel BorelFamilyBasic ContinuousBorelPreimages
  HausdorffDiameterCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [orthogonal_projection_outer_volume_bound]: supporting
    outer-measure form of the Fubini–isodiametric estimate in
    2.10.46, p. 203. No measurability or boundedness
    premise is added to the set. *)
Theorem orthogonal_projection_outer_volume_bound (R : realType) m k
    (p : {linear R_n R (m+k) -> R_n R k})
    (S : set (inner_metric_space (@euclidean_inner_productP R (m+k)))) :
  O_star p -> (euclidean_lebesgue_measure (m+k) S<=
    euclidean_lebesgue_measure k (p @` S)*hausdorff_diameter_cost m S)%E.
Proof.
move=> hp.
pose X := [the metricType R of inner_metric_space (@euclidean_inner_productP R (m+k))].
pose Y := [the metricType R of inner_metric_space (@euclidean_inner_productP R k)].
have hm := euclidean_lebesgue_is_measure R (m+k).
have hn := euclidean_lebesgue_is_measure R k.
have hr := euclidean_lebesgue_borel_regular R (m+k).
have hs := euclidean_lebesgue_borel_regular R k.
have [q hq] := euclidean_projection_linear_complete hp.
have hpcont : continuous (p : X -> Y).
  have he : (p : X -> Y)=euclidean_projection_linear q by apply: funext=> x; exact: esym (hq x).
  rewrite he; exact: euclidean_projection_continuous.
have [C [hPC [hC he]]] := borel_regular_cover hs (p @` S).
pose B : set X := closure S `&` (p @^-1` C).
have hB : borel_set B.
  apply: (@borel_family_binary_intersection X setT _ (borel_sets_family X)).
  - exact (@closed_borel_set X (closure S) (@closed_closure X S)).
  - exact (@continuous_borel_preimage X Y p hpcont C hC).
have hSB : S `<=` B by move=> x hx; split; [exact: subset_closure hx|apply: hPC; by exists x].
have hBC : p @` B `<=` C by move=> y [x [_ hx] <-].
pose D := @orthogonal_projection_chart R m k p hp.
have hD := @orthogonal_projection_chart_specification R m k p hp.
have hb := @projection_chart_volume_support_bound R m k p D.1 D.2 hD B C
  (borel_regular_borel_measurable hm hr hB) (borel_regular_borel_measurable hn hs hC) hBC.
apply: le_trans (measure_mono hm hSB) _.
apply: le_trans hb _; rewrite -he.
apply: lee_wpmul2l; first exact (measure_nonnegative hn (p @` S)).
rewrite -[hausdorff_diameter_cost m S]hausdorff_diameter_cost_closure.
apply: hausdorff_diameter_cost_monotone; by move=> x [hx _].
Qed.
