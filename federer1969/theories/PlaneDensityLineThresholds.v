(** Federer (1969), 2.5.10, p. 101: the geometric meaning of a representing
    density on unit horizontal and vertical segments. We use threshold sets
    instead of assuming a bounded density or sigma-finiteness of H^1 on the
    plane. The chosen unit segments and threshold c in (0,1) make the
    implicit contradiction concrete. Source context: PlaneLineMeasures.v and
    RepresentingDensitySetBounds.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MeasureUP MeasureBasic
  MeasureFiniteClosure MeasureAlmostBasic MeasureNullModification BorelRegularMeasureUP
  HausdorffLength LebesgueScalarMeasure PlaneLineMeasures PlaneProjectionMeasure PlaneProjectionFunctional
  PlaneDensityThresholdBounds TotalScalarThresholdSets ImageTraceSets
  TotalScalarLpUP RealLatticeDensityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section LineThresholds.
Variable R : realType.
Local Notation X := [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)].
Local Notation H := (@hausdorff_length R X).
Local Notation I := (`[0%R,1%R] : set R).

(** Source for [plane_density_vertical_superlevel_null]:
    vertical part of the non-L^2-measurability argument
    in Federer 2.5.10, p. 101. The scalar
    parameter set where k exceeds any c>0 on a
    vertical unit segment has Lebesgue length zero. *)
Theorem plane_density_vertical_superlevel_null (k : X -> R) (c s : R) :
  is_real_lattice_density H (total_scalar_lp H 1) (@plane_projection_functional R) k ->
  (0<c)%R -> lebesgue_scalar_measure [set t | I t /\ (c<k (plane_vertical s t))%R]=0.
Proof.
move=> hk hc.
pose E := (plane_vertical s @` I) `&` [set x | (c<k x)%R].
have hsub : E `<=` plane_vertical s @` I by move=> x [hx _].
have hE : measure_measurable H E.
  apply: (@measure_measurable_intersection R X H (@hausdorff_length_is_measure R X)).
  - exact (@borel_regular_borel_measurable R X H (@hausdorff_length_is_measure R X)
      (@hausdorff_length_borel_regular R X) _ (@plane_vertical_segment_borel R s 0%R 1%R)).
  - exact (@total_scalar_strict_upper_measurable R X H (@hausdorff_length_is_measure R X) k c hk.1).
have hseg : H (plane_vertical s @` I) = 1.
  by rewrite plane_vertical_hausdorff lebesgue_scalar_segment ?ler01 // subr0.
have hf : H E < +oo.
  apply: le_lt_trans (@measure_mono R X H (@hausdorff_length_is_measure R X) _ _ hsub) _.
  by rewrite hseg ltry.
have hpsi : plane_projection_measure E=0.
  exact (@measure_null_subset R X (@plane_projection_measure R) (plane_projection_is_measure R)
    E _ hsub (@plane_vertical_segment_projection_null R s 0%R 1%R)).
have hzero : H E=0.
  apply: (@plane_density_vertical_threshold_null R k E c hk hE hf hpsi hc)=> x [_ hx].
  exact: ltW hx.
have he : E=plane_vertical s @` [set t | I t /\ (c<k (plane_vertical s t))%R].
  by rewrite /E image_intersection_trace.
by rewrite he plane_vertical_hausdorff in hzero.
Qed.

(** Source for [plane_density_horizontal_sublevel_null]:
    horizontal part of the density argument in Federer
    2.5.10, p. 101. The parameter set where
    k is at most any c<1 on a horizontal unit
    segment has Lebesgue length zero. *)
Theorem plane_density_horizontal_sublevel_null (k : X -> R) (c t : R) :
  is_real_lattice_density H (total_scalar_lp H 1) (@plane_projection_functional R) k ->
  (c<1)%R -> lebesgue_scalar_measure [set s | I s /\ (k (plane_horizontal t s)<=c)%R]=0.
Proof.
move=> hk hc.
pose E := (plane_horizontal t @` I) `&` [set x | (k x<=c)%R].
have hsub : E `<=` plane_horizontal t @` I by move=> x [hx _].
have hE : measure_measurable H E.
  apply: (@measure_measurable_intersection R X H (@hausdorff_length_is_measure R X)).
  - exact (@borel_regular_borel_measurable R X H (@hausdorff_length_is_measure R X)
      (@hausdorff_length_borel_regular R X) _ (@plane_horizontal_segment_borel R t 0%R 1%R)).
  - exact (@total_scalar_closed_lower_measurable R X H (@hausdorff_length_is_measure R X) k c hk.1).
have hseg : H (plane_horizontal t @` I) = 1.
  by rewrite plane_horizontal_hausdorff lebesgue_scalar_segment ?ler01 // subr0.
have hf : H E < +oo.
  apply: le_lt_trans (@measure_mono R X H (@hausdorff_length_is_measure R X) _ _ hsub) _.
  by rewrite hseg ltry.
have he : E=plane_horizontal t @` [set s | I s /\ (k (plane_horizontal t s)<=c)%R].
  by rewrite /E image_intersection_trace.
have hpsi : plane_projection_measure E=H E.
  by rewrite he plane_horizontal_projection_measure plane_horizontal_hausdorff.
have hzero : H E=0.
  apply: (@plane_density_horizontal_threshold_null R k E c hk hE hf hpsi hc)=> x [_ hx].
  exact hx.
by rewrite he plane_horizontal_hausdorff in hzero.
Qed.

(** Source for [plane_density_horizontal_superlevel_one]:
    the horizontal superlevel occupies the full unit
    segment in the Fubini contradiction of Federer
    2.5.10, p. 101. This is the null-modification
    consequence of the preceding sublevel test. *)
Theorem plane_density_horizontal_superlevel_one (k : X -> R) (c t : R) :
  is_real_lattice_density H (total_scalar_lp H 1) (@plane_projection_functional R) k ->
  (c<1)%R -> lebesgue_scalar_measure [set s | I s /\ (c<k (plane_horizontal t s))%R] = 1.
Proof.
move=> hk hc.
have hz := @plane_density_horizontal_sublevel_null k c t hk hc.
have he : lebesgue_scalar_measure [set s | I s /\ (c<k (plane_horizontal t s))%R]=lebesgue_scalar_measure I.
  apply: (@measure_null_modification_value R R (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R)
    _ I [set s | I s /\ (k (plane_horizontal t s)<=c)%R] hz)=> s hs; split.
  - by move=> [hI _].
  - move=> hI; split=> //; rewrite ltNge; apply/negP=> hle; apply: hs; by split.
by rewrite he lebesgue_scalar_segment ?ler01 // subr0.
Qed.
End LineThresholds.
