(** Federer (1969), 3.2.22, p. 259: use
    the actual differential chart points of 3.2.19
    in source parameters, then transport their exceptional
    sets to the source-chart image by 2.10.11. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP
  RectifiableCompactChartsUP RectifiableCompactChartLaws RectifiableDifferentialChartUP
  RectifiableChartDensityDifferential EuclideanChartAlmostPullback EuclideanRectifiableNullImage
  EuclideanLebesgueDimensions HausdorffMeasure MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_parameter_chart_points_almost]:
    the source-chart approximate differential and tangent
    identities in Federer 3.2.19, p. 256,
    used in 3.2.22, p. 259. The
    inverse chart transports the image-null exceptional set
    back to a Lebesgue-null parameter set. *)
Lemma rectifiable_parameter_chart_points_almost (R:realType) m n v
    (lambda:R) (W:set (R_n R n)) (K:set (R_n R m))
    (psi:R_n R m->R_n R n) (F:R_n R n->R_n R v):
  1<lambda ->is_uniform_compact_rectifiable_chart lambda K psi ->
  psi @` K `<=` W ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W< +oo)%E ->
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R v)) setT F ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m) K
    [set a|is_rectifiable_differential_chart_point W K psi F (psi a)].
Proof.
move=>hLambda hChart hKW hW hFinite hF.
have hLocal:=rectifiable_chart_density_differential hLambda hChart hKW hW hFinite hF.
have hPoint:measure_almost_everywhere_on (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) (psi @` K)
    [set w|is_rectifiable_differential_chart_point W K psi F w].
  apply:(measure_null_subset (@hausdorff_measure_is_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) _ hLocal)=>w [hw hn].
  split; first exact hw; by move=>[_ hP]; exact:hn hP.
exact:(euclidean_chart_almost_pullback (uniform_compact_chart_bilipschitz hChart) hPoint).
Qed.

(** Source for [euclidean_lipschitz_almost_pushforward]:
    the source-chart null-exception transfer in Federer
    3.2.19, p. 256, also used in 3.2.22,
    p. 259. A property holding almost everywhere
    in the parameters holds H^m almost everywhere
    on their image, by 2.10.11. Injectivity and
    source-set measurability are not needed for this direction. *)
Lemma euclidean_lipschitz_almost_pushforward (R:realType) m n
    (psi:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (A:set (R_n R m)) (P:set (R_n R n)):
  is_metric_lipschitz setT psi ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m) A [set a|P (psi a)] ->
  measure_almost_everywhere_on (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) (psi @` A) P.
Proof.
move=>hPsi hAE; have hImage:=euclidean_lipschitz_null_image hPsi hAE.
apply:(measure_null_subset (@hausdorff_measure_is_measure R
  (inner_metric_space (@euclidean_inner_productP R n)) m) _ hImage)=>w [[a ha hValue] hNot].
exists a; last exact hValue; split; first exact ha.
change (~P (psi a)); by rewrite hValue.
Qed.
