(** Federer (1969), 3.3.18, p. 301: positive original upper
    density almost everywhere on an actual rectifiable carrier. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric RectifiableSetUP
  RectifiableFiniteHausdorffMass FiniteHausdorffZeroUpperDensityNull
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic RegularMeasureUP
  HausdorffMeasure MetricDensities MetricDensityNumericalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countably_rectifiable_positive_upper_density]: the
    compact-carrier nullity and countable assembly in the proof of
    Federer 3.3.18, p. 301. Each actual bounded rectifiable image
    has finite Hausdorff mass; actual 2.10.19(1) makes its original
    zero-upper-density subset null. The original carrier need not
    be measurable, and its total mass need not be finite. *)
Theorem countably_rectifiable_positive_upper_density (R:realType) n m
    (psi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_measure psi ->is_regular_measure psi ->is_countably_m_rectifiable m S ->
  measure_almost_everywhere_on psi S [set a|0<upper_metric_density m psi a].
Proof.
move=>hPsi hRegular [C [hC [hRect hUnion]]].
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose P:=[set a:X|0<upper_metric_density m psi a].
pose F A:=A `\` P.
have hNull A:C A ->psi (F A)= 0.
  move=>hA.
  apply:(@finite_hausdorff_zero_upper_density_null R [the metricType R of X] m psi (F A) hPsi hRegular).
  - apply:(le_lt_trans _ (rectifiable_finite_hausdorff_mass (hRect A hA))).
    apply:(measure_mono (@hausdorff_measure_is_measure R [the metricType R of X] m)).
    by move=>x [hx _].
  - move=>a [_ hNot].
    have hNonnegative:=(@metric_densities_nonnegative R [the metricType R of X] m psi a hPsi).2.
    apply/eqP; rewrite eq_le hNonnegative andbT leNgt.
    by apply/negP.
have hUnionNull:=@measure_null_countable_union R [the choiceType of X]
  [the choiceType of set X] psi hPsi C F hC hNull.
apply:(@measure_null_subset R [the choiceType of X] psi hPsi _ _ _ hUnionNull).
move=>x [hx hn]; rewrite hUnion in hx; have [A hA hxA]:=hx.
exists A; first exact:hA.
by split.
Qed.
