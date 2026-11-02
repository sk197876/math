(** Federer (1969), 3.2.18, p. 255:
    consequences of the independent compact-chart
    laws. Inverse inequalities give actual
    univalence, while global bounds give continuity
    and hence compact measurable image pieces. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  LipschitzUP LipschitzBasic NormMetricScaleContinuity MetricBiLipschitzUP MetricBiLipschitzInverse
  RectifiableCompactChartsUP MeasureUP BorelRegularMeasureUP TopologicalBorel
  HausdorffMeasure HausdorffClosedCoverAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [uniform_compact_chart_bilipschitz]:
    the restriction and inverse bounds in
    Federer 3.2.18, p. 255, expressed
    through the independent two-distance-law predicate. *)
Lemma uniform_compact_chart_bilipschitz (R : realType) m n (lambda : R)
    (K : set (R_n R m)) (psi : R_n R m -> R_n R n) :
  is_uniform_compact_rectifiable_chart lambda K psi ->
  @is_metric_bilipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R m))
    (inner_metric_space (@euclidean_inner_productP R n)) K psi lambda.
Proof.
move=> hChart; split.
- apply: (metric_lipschitz_bound_restrict (fun _ _=>I)).
  exact: rectifiable_chart_global_bound hChart.
- move=> x y hx hy.
  exact: (@rectifiable_chart_inverse_bound R m n lambda K psi hChart x y hx hy).
Qed.

(** Source for [uniform_compact_chart_injective]: actual
    univalence of psi_i restricted to K_i,
    Federer 3.2.18, p. 255. No
    arbitrary target-wide inverse is introduced. *)
Lemma uniform_compact_chart_injective (R : realType) m n (lambda : R)
    (K : set (R_n R m)) (psi : R_n R m -> R_n R n) :
  is_uniform_compact_rectifiable_chart lambda K psi ->
  forall x y, K x -> K y -> psi x=psi y -> x=y.
Proof.
move=> hChart.
exact: metric_bilipschitz_injective_on (uniform_compact_chart_bilipschitz hChart).
Qed.

(** Source for [uniform_compact_chart_image_compact]:
    compactness of each image piece in
    Federer 3.2.18, p. 255, from
    compact K_i and the global Lipschitz law. *)
Lemma uniform_compact_chart_image_compact (R : realType) m n (lambda : R)
    (K : set (R_n R m)) (psi : R_n R m -> R_n R n) :
  is_uniform_compact_rectifiable_chart lambda K psi ->
  @compact (inner_metric_space (@euclidean_inner_productP R n)) (psi @` K).
Proof.
move=> hChart.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose Y := inner_metric_space (@euclidean_inner_productP R n).
have hLip := rectifiable_chart_global_bound hChart.
have hCont : continuous (fun x : X=>(psi x:Y)).
  apply: (@metric_fixed_lipschitz_continuous R X Y psi lambda hLip.1).
  by move=> x y; exact: hLip.2 x y I I.
exact: continuous_compact (continuous_subspaceT hCont) (rectifiable_chart_compact hChart).
Qed.

(** Source for [rectifiable_chart_piece_measurable]:
    measurability of the disjoint compact image
    pieces in Federer 3.2.18, p. 255.
    Metric Hausdorff measure is Borel regular;
    local finiteness on the ambient space is
    neither assumed nor needed. *)
Lemma rectifiable_chart_piece_measurable (R : realType) m n (lambda : R)
    (W C : set (R_n R n)) :
  @is_rectifiable_chart_piece R m n lambda W C ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) C.
Proof.
move=> [_ [K [psi [hChart ->]]]].
pose Y := inner_metric_space (@euclidean_inner_productP R n).
have hClosed := compact_closed (@metric_hausdorff R Y) (uniform_compact_chart_image_compact hChart).
exact: (borel_regular_borel_measurable (@hausdorff_measure_is_measure R Y m)
  (@hausdorff_measure_borel_regular R Y m) (closed_borel_set hClosed)).
Qed.

(** Source for [empty_uniform_compact_chart]: empty
    compact slots in the countable sequence
    of Federer 3.2.18, p. 255.
    The auxiliary zero map obeys the
    prescribed nonnegative global bound, and
    every pointwise obligation on K is vacuous. *)
Lemma empty_uniform_compact_chart (R : realType) m n (lambda : R) :
  0<=lambda -> @is_uniform_compact_rectifiable_chart R m n lambda set0 (fun _=>0).
Proof.
move=> hLam; constructor.
- exact: compact0.
- split=> // x y _ _.
  change (is_true (mdist (0 : inner_metric_space (@euclidean_inner_productP R n)) 0<=
    lambda*mdist (x : inner_metric_space (@euclidean_inner_productP R m)) y)).
  rewrite mdistxx; exact: (mulr_ge0 hLam (mdist_ge0 _ _)).
- by move=> x y [].
- by move=> a [].
Qed.
