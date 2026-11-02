(** Federer (1969), 3.2.26(2), p. 261: reduce
    the comparison to the compact pieces of 3.2.18.
    Each such piece is a finite rectifiable measurable set,
    so its own restricted Hausdorff measure has density one
    almost everywhere by 3.2.19, p. 256. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RectifiableSetUP RectifiableCompactChartsUP RectifiableCompactChartLaws RectifiableDensityTangent
  EuclideanLipschitzRectifiableImage CompactLipschitzImageMass LipschitzUP LipschitzBasic
  HausdorffMeasure HausdorffClosedCoverAgreement MetricDensities PartialFunctionUP
  MeasureUP MeasureBasic MeasureRestriction MeasureAlmostUP MeasureAlmostBasic
  BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [uniform_compact_chart_finite_rectifiable]: the
    compact-piece reduction in 3.2.26(2), p. 261.
    Bounded Lipschitz images are countably rectifiable; compact
    parameter mass and the Hausdorff image bound give finite
    H^m measure, also in degree zero. *)
Lemma uniform_compact_chart_finite_rectifiable (R:realType) m n (lambda:R)
    (K:set (R_n R m)) (psi:R_n R m->R_n R n):
  is_uniform_compact_rectifiable_chart lambda K psi ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m (psi @` K).
Proof.
move=>hChart.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
have hGlobal:=metric_lipschitz_of_bound (rectifiable_chart_global_bound hChart).
have hLocal:@is_metric_lipschitz R X Y K psi.
  have [L [hL hBound]]:=hGlobal; exists L; split; first exact hL.
  exact:(@metric_lipschitz_bound_restrict R X Y setT K psi L (subsetT K) hBound).
split; last exact:(compact_lipschitz_image_finite_hausdorff_mass hGlobal (rectifiable_chart_compact hChart)).
split; first exact:hausdorff_measure_is_measure.
exists (psi @` K); split.
- exact:(@euclidean_lipschitz_image_countably_rectifiable R m Y K psi hLocal).
- by rewrite /measure_almost_included setDv (measure_empty (@hausdorff_measure_is_measure R Y m)).
Qed.

(** Source for [uniform_compact_chart_upper_density_one]: the
    almost-everywhere unit density used in the ball family of
    3.2.26(2), p. 261. This is 3.2.19 applied
    to the compact image itself, not an extra density
    assumption imposed on the chart. *)
Lemma uniform_compact_chart_upper_density_one (R:realType) m n (lambda:R)
    (K:set (R_n R m)) (psi:R_n R m->R_n R n):
  is_uniform_compact_rectifiable_chart lambda K psi ->
  measure_almost_everywhere_on (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) (psi @` K) [set w|
    upper_metric_density m (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) (psi @` K)) w= 1].
Proof.
move=>hChart.
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R Y m.
have hH:=@hausdorff_measure_is_measure R Y m.
have hMeas:@borel_set Y (psi @` K).
  exact:(closed_borel_set (compact_closed (@metric_hausdorff R Y)
    (uniform_compact_chart_image_compact hChart))).
have hRect:=uniform_compact_chart_finite_rectifiable hChart.
have hDensity:=(federer_3_2_19 hRect
  (borel_regular_borel_measurable hH (@hausdorff_measure_borel_regular R Y m) hMeas)).1.
apply:(measure_null_subset hH _ hDensity)=>w [hw hn]; split; first exact hw.
move=>[hGraph _]; apply:hn.
exact:((@metric_density_graph R Y m (measure_restrict H (psi @` K)) w 1).1 hGraph).1.
Qed.
