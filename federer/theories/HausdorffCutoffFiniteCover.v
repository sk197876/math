(** Federer (1969), 2.10.45, printed p. 203: bound the Hausdorff cutoff cost
    by the sum of the costs of the finitely many product covering pieces
    associated with each T. These elementary consequences of the abstract
    cutoff infimum allow empty pieces and zero diameter; no measurability of
    the pieces or covered target is assumed. Source context:
    SquaredMetricProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology HausdorffLengthUP HausdorffMeasureUP
  HausdorffDiameterCost HausdorffPowerCostLaws MetricDiameterUP MetricDiameter
  MetricScaleEnvelopeUP MetricScaleEnvelopeLaws MetricScaleCutoffCost
  NonnegativeSum NonnegativeSumSupport MeasureUP MeasureBasic FiniteCoverMeasureBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_cutoff_finite_diameter_bound]: supporting
    one-piece cutoff-cost bound for the last
    display of 2.10.45, p. 203. The
    piece may be empty, and its nonnegative
    diameter upper bound may be zero. *)
Lemma hausdorff_cutoff_finite_diameter_bound (R : realType) (X : metricType R)
    d delta (nu : set X -> \bar R) A (r : R) :
  @is_metric_scale_envelope R X (@nonempty_metric_sets R X)
    (fun j=>val j) (fun j=>hausdorff_diameter_cost d (val j)) delta nu ->
  (0<=r)%R -> r%:E<=delta -> extended_metric_diameter A<=r%:E ->
    nu A<=(hausdorff_normalisation R d*r^+d)%R%:E.
Proof.
move=> hn hr hcap hA.
have hm : is_measure nu := metric_scale_envelope_is_measure hn
  (fun j=>hausdorff_diameter_cost_nonnegative d (val j)).
case: (pselect (A !=set0))=> [hne|hempty]; last first.
  have -> : A=set0 by apply/seteqP; split=> x hx //; exfalso; apply: hempty; by exists x.
  rewrite (measure_empty hm) lee_fin.
  exact: mulr_ge0 (ltW (hausdorff_normalisation_positive R d)) (exprn_ge0 _ hr).
pose j : @nonempty_metric_sets R X := Sub A (mem_set hne).
have hdiam : extended_metric_diameter A<=delta := le_trans hA hcap.
have hb : nu A<=nonnegative_sum [set j] (fun q=>hausdorff_diameter_cost d (val q)).
  apply: (@metric_scale_envelope_lower R X (@nonempty_metric_sets R X)
    (fun q=>val q) (fun q=>hausdorff_diameter_cost d (val q)) delta nu hn A [set j] (countable1 j)).
  - by move=> q ->.
  - move=> x hx; by exists j.
rewrite nonnegative_sum_singleton in hb; last exact: hausdorff_diameter_cost_nonnegative.
apply: le_trans hb _; rewrite -hausdorff_power_cost_finite /hausdorff_diameter_cost.
exact: hausdorff_power_cost_monotone (metric_diameter_nonnegative (extended_metric_diameter_specification A)) hA.
Qed.

(** Source for [hausdorff_cutoff_finite_equal_diameter_cover]: supporting
    finite inner sum in the last display
    of 2.10.45, p. 203. Every piece
    has the same finite diameter upper bound;
    neither nonemptiness nor measurable overlap is required. *)
Theorem hausdorff_cutoff_finite_equal_diameter_cover (R : realType) (X : metricType R)
    (I : finType) d delta (nu : set X -> \bar R) A (S : I -> set X) (r : R) :
  @is_metric_scale_envelope R X (@nonempty_metric_sets R X)
    (fun j=>val j) (fun j=>hausdorff_diameter_cost d (val j)) delta nu ->
  (0<=r)%R -> r%:E<=delta ->
  (forall i, extended_metric_diameter (S i)<=r%:E) ->
  A `<=` \bigcup_i S i ->
    nu A<=(#|I|%:R*(hausdorff_normalisation R d*r^+d))%R%:E.
Proof.
move=> hn hr hcap hdiam hcover.
have hm : is_measure nu := metric_scale_envelope_is_measure hn
  (fun j=>hausdorff_diameter_cost_nonnegative d (val j)).
have hb := @measure_finite_indexed_cover R X I nu hm A S hcover.
have he : (\sum_(i : I) (hausdorff_normalisation R d*r^+d)%R%:E)=
    (#|I|%:R*(hausdorff_normalisation R d*r^+d))%R%:E.
  rewrite sumEFin sumr_const cardT; congr (_%:E); symmetry; exact: mulr_natl.
rewrite -he; apply: le_trans hb _; apply: lee_sum=> i _.
exact: hausdorff_cutoff_finite_diameter_bound hn hr hcap (hdiam i).
Qed.
