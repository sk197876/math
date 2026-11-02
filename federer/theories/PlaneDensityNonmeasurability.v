(** Federer (1969), 2.5.10, p. 101: every H^1 measurable density
    representing the geometric functional fails to be L^2 measurable. The
    proof makes the suggested geometric reflection explicit: the threshold
    set in the unit square has null vertical sections and full horizontal
    sections, contradicting 2.6.2(3), pp. 115, 117, and the Cartesian L^2
    identification 2.6.5, pp. 119–120. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric EuclideanInnerProduct InnerMetric RealMetricBackground EuclideanPlaneCoordinates EuclideanPlaneLebesgue
  EuclideanLebesgueDimensions MeasureUP MeasureBasic MeasureFiniteClosure BorelRegularMeasureUP
  TopologicalBorel IntervalBumpFunctions HausdorffLength LebesgueScalarMeasure
  ProductMeasure ProductRectangleValue ProductSections ProductSectionObstruction CountablyMeasurableUP
  CountablyMeasurableProduct CountablyMeasurableSubsets TotalScalarLpUP RealLatticeDensityUP
  MeasurableFunctionUP TotalScalarThresholdSets PlaneProjectionFunctional PlaneProjectionFormula
  PlaneLineMeasures PlaneDensityLineThresholds ContinuumHypothesisUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [plane_projection_density_not_lebesgue_measurable]:
    direct final geometric claim of Federer 2.5.10,
    p. 101. No CH hypothesis is needed for the
    obstruction itself: every representing density has
    the incompatible line tests. CH is used separately
    to ensure that such a density exists. *)
Theorem plane_projection_density_not_lebesgue_measurable (R : realType)
    (k : inner_metric_space (@euclidean_inner_productP R 2) -> R) :
  is_real_lattice_density (@hausdorff_length R _) (total_scalar_lp (@hausdorff_length R _) 1)
    (@plane_projection_functional R) k ->
  ~ @is_measure_measurable_function R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R 2)]
    [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)]
    (@euclidean_lebesgue_measure R 2) (total_scalar_function k).
Proof.
move=> hk hkm.
pose X := [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)].
pose h := lebesgue_scalar_is_measure R.
pose mu := product_measure h h.
pose I : set R := `[0%R,1%R].
pose c : R := (2^-1)%R.
have hc0 : (0<c)%R by rewrite /c invr_gt0 ltr0n.
have hc1 : (c<1)%R by rewrite /c invf_lt1 // ltr1n.
pose K : set X := [set x | (c<k x)%R].
pose S : set (R*R) := (I `*` I) `&` ((@euclidean_plane_join R) @^-1` K).
have hK : measure_measurable (@euclidean_lebesgue_measure R 2) K.
  exact (@total_scalar_strict_upper_measurable R X (@euclidean_lebesgue_measure R 2)
    (euclidean_lebesgue_is_measure R 2) k c hkm).
have hI : measure_measurable (@lebesgue_scalar_measure R) I.
  apply: (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) h (lebesgue_scalar_borel_regular R)).
  apply: closed_borel_set; exact: segment_closed_real.
have hSm : measure_measurable mu S.
  apply: (@measure_measurable_intersection R [the choiceType of (R*R)%type] mu (product_measure_is_measure h h)).
  - exact: (product_measure_measurable_rectangle h h hI hI).1.
  - exact (@euclidean_plane_lebesgue_preimage_measurable R K hK).
have hSc : measure_countably_measurable mu S.
  apply: (@measurable_subset_countably_measurable R [the choiceType of (R*R)%type]
    mu (product_measure_is_measure h h) S setT hSm (fun x hx => Logic.I)).
  exact: product_whole_countably_measurable (lebesgue_scalar_countably_measurable R) (lebesgue_scalar_countably_measurable R).
apply: (@incompatible_positive_horizontal_sections R R R (@lebesgue_scalar_measure R)
  (@lebesgue_scalar_measure R) h h S I hSc).
- move=> s; case: (pselect (I s))=> hs.
  + have he : product_vertical_section S s=[set t | I t /\ (c<k (plane_vertical s t))%R].
      apply/seteqP; split=> t; [by move=> [[_ ht] hk']|by move=> [ht hk']; split=> //; split].
    rewrite he; exact (@plane_density_vertical_superlevel_null R k c s hk hc0).
  + have he : product_vertical_section S s=set0.
      apply/seteqP; split=> t; last by [].
      by move=> [[hsi _] _]; exact: hs hsi.
    by rewrite he (measure_empty h).
- move=> t ht.
  have he : product_horizontal_section S t=[set s | I s /\ (c<k (plane_horizontal t s))%R].
    apply/seteqP; split=> s; [by move=> [[hs _] hk']|by move=> [hs hk']; split=> //; split].
  by rewrite he (@plane_density_horizontal_superlevel_one R k c t hk hc1) lte01.
- by rewrite /I lebesgue_scalar_segment ?ler01 // subr0 lte01.
Qed.

(** Source for [federer_2_5_10_geometric_example]: the
    unexpected example in Federer 2.5.10, p. 101,
    with the actual H^1 measure, actual fibre-sum
    functional, and actual L^2 measure. Under CH a
    representing H^1 measurable density exists, and
    every such density fails to be L^2 measurable. *)
Theorem federer_2_5_10_geometric_example (R : realType) : continuum_hypothesis ->
  exists k : inner_metric_space (@euclidean_inner_productP R 2) -> R,
    is_real_lattice_density (@hausdorff_length R _) (total_scalar_lp (@hausdorff_length R _) 1)
      (@plane_projection_functional R) k /\
    ~ @is_measure_measurable_function R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R 2)]
    [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)]
    (@euclidean_lebesgue_measure R 2) (total_scalar_function k).
Proof.
move=> hCH; have [k hk] := @plane_projection_density_under_continuum R hCH.
exists k; split=> //; exact: plane_projection_density_not_lebesgue_measurable hk.
Qed.
