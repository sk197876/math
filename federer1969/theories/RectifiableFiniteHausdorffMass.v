(** Federer (1969), 3.2.23, p. 260: an m-rectifiable first
    factor has finite H^m mass. This supporting fact follows from
    the bounded parametrization in 3.2.14, pp. 251–252, the
    extension theorem and the Lipschitz Hausdorff image bound. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RectifiableSetUP RectifiableElementary EuclideanRectifiableGlobalParametrization
  MetricBoundedClosureLaws CompactLipschitzImageMass HausdorffMeasure HausdorffCountingMeasure
  CountingMeasure MeasureUP MeasureBasic MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_finite_hausdorff_mass]: supporting
    finite first-factor mass in Federer 3.2.23, p. 260.
    The actual bounded parametrizing set need not be measurable.
    In dimension zero a finite set may have several points. *)
Theorem rectifiable_finite_hausdorff_mass (R:realType) m n (W:set (R_n R n)):
  (@is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n)) m W) ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W< +oo.
Proof.
case:m=>[|m] hW.
- have [F ->]:=finite_fsetP.1 hW.
  by rewrite hausdorff_zero_counting_measure counting_measure_finite; exact:ltry.
- have [A [f [hA [hf hImage]]]]:=positive_rectifiable_global_parametrization hW.
  have hFinite:=compact_lipschitz_image_finite_hausdorff_mass hf
    (euclidean_bounded_closure_compact hA).
  apply:(le_lt_trans _ hFinite).
  apply:(measure_mono (@hausdorff_measure_is_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m.+1)).
  move=>w hw; rewrite -hImage in hw; have [x hx hfx]:=hw.
  exists x; first exact:subset_closure hx.
  exact hfx.
Qed.

(** Source for [rectifiable_hausdorff_measure_rectifiable]: supporting
    application of the compact-chart decomposition in Federer 3.2.23,
    p. 260. Actual m-rectifiability implies the finite-mass
    (H^m,m) version; the converse is not asserted. *)
Lemma rectifiable_hausdorff_measure_rectifiable (R:realType) m n (W:set (R_n R n)):
  (@is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n)) m W) ->is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W.
Proof.
move=>hW; split; last exact:rectifiable_finite_hausdorff_mass hW.
split; first exact:hausdorff_measure_is_measure.
exists W; split; first exact:rectifiable_countably_rectifiable hW.
by rewrite /measure_almost_included setDv (measure_empty (@hausdorff_measure_is_measure R
  (inner_metric_space (@euclidean_inner_productP R n)) m)).
Qed.
