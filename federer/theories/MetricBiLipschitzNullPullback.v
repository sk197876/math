(** Federer (1969), 3.2.20, p. 257: transfer the
    almost-everywhere differential identity from each chart image to its
    compact parameter set, using the inverse Lipschitz comparison
    of 2.10.11, p. 176. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  HausdorffMeasure MetricBiLipschitzUP MetricBiLipschitzHausdorff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_bilipschitz_null_pullback]: supporting null-set
    pullback through a compact chart in Federer 3.2.20, p. 257.
    Neither the exceptional set nor its preimage is assumed measurable;
    the actual inverse Hausdorff inequality proves it null. *)
Lemma metric_bilipschitz_null_pullback (R : realType) (X Y : metricType R)
    (K A : set X) (f : X -> Y) (lambda : R) m (x0 : X) (B : set Y) :
  is_metric_bilipschitz_bound K f lambda -> A `<=` K -> f @` A `<=` B ->
  @hausdorff_measure R Y m B=0 -> @hausdorff_measure R X m A=0.
Proof.
move=> hBi hAK hImage hNull.
have hmX := @hausdorff_measure_is_measure R X m.
have hmY := @hausdorff_measure_is_measure R Y m.
have hImgNull := measure_null_subset hmY hImage hNull.
have hBound := (@metric_bilipschitz_hausdorff_bounds R X Y K f lambda x0 m A hBi hAK).2.
rewrite hImgNull mule0 in hBound.
by apply/eqP; rewrite eq_le hBound (measure_nonnegative hmX).
Qed.

(** Source for [metric_bilipschitz_almost_pullback]: almost-everywhere
    chart-image to parameter-set transfer in Federer 3.2.20,
    p. 257. The exception sets are counted only on the
    original chart domain and image. *)
Theorem metric_bilipschitz_almost_pullback (R : realType) (X Y : metricType R)
    (K : set X) (f : X -> Y) (lambda : R) m (x0 : X) (P : set Y) :
  is_metric_bilipschitz_bound K f lambda ->
  measure_almost_everywhere_on (@hausdorff_measure R Y m) (f @` K) P ->
  measure_almost_everywhere_on (@hausdorff_measure R X m) K [set x | P (f x)].
Proof.
move=> hBi hAE.
apply: (@metric_bilipschitz_null_pullback R X Y K (K `\` [set x | P (f x)])
  f lambda m x0 ((f @` K) `\` P) hBi _ _ hAE).
- by move=> x hx; exact hx.1.
- move=> y [x [hx hn] <-]; split; [by exists x|exact hn].
Qed.
