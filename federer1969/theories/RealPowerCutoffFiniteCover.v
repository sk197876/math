(** Federer (1969), 3.4.2(8), pp. 315–316: finite cube-image covers
    bound each positive-cutoff Hausdorff cost in the actual real degree. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology HausdorffLengthUP RealPower MetricRealPowerCost MetricDiameterUP MetricDiameter
  MetricScaleEnvelopeUP MetricScaleEnvelopeLaws MetricScaleCutoffCost
  NonnegativeSum NonnegativeSumSupport MeasureUP MeasureBasic FiniteCoverMeasureBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_power_cutoff_finite_diameter_bound]: supporting
    one-piece cutoff-cost bound for the last
    display of 3.4.2(8), pp. 315–316. The
    piece may be empty, and its nonnegative
    diameter upper bound may be zero. *)
Lemma real_power_cutoff_finite_diameter_bound (R : realType) (X : metricType R)
    (c p : R) delta (nu : set X -> \bar R) A (r : R) :
  @is_metric_scale_envelope R X (@nonempty_metric_sets R X)
    (fun j=>val j) (fun j=>metric_real_diameter_cost c p (val j)) delta nu ->
  (0<=c)%R -> (0<=p)%R -> (0<=r)%R -> r%:E<=delta -> extended_metric_diameter A<=r%:E ->
    nu A<=(c*real_power r p)%R%:E.
Proof.
move=> hn hc hp hr hcap hA.
have hm : is_measure nu := metric_scale_envelope_is_measure hn
  (fun j=>metric_real_power_cost_nonnegative p (extended_metric_diameter (val j)) hc).
case: (pselect (A !=set0))=> [hne|hempty]; last first.
  have -> : A=set0 by apply/seteqP; split=> x hx //; exfalso; apply: hempty; by exists x.
  rewrite (measure_empty hm) lee_fin.
  exact: mulr_ge0 hc (real_power_nonnegative r p).
pose j : @nonempty_metric_sets R X := Sub A (mem_set hne).
have hdiam : extended_metric_diameter A<=delta := le_trans hA hcap.
have hb : nu A<=nonnegative_sum [set j] (fun q=>metric_real_diameter_cost c p (val q)).
  apply: (@metric_scale_envelope_lower R X (@nonempty_metric_sets R X)
    (fun q=>val q) (fun q=>metric_real_diameter_cost c p (val q)) delta nu hn A [set j] (countable1 j)).
  - by move=> q ->.
  - move=> x hx; by exists j.
rewrite nonnegative_sum_singleton in hb; last exact: metric_real_power_cost_nonnegative hc.
apply: le_trans hb _; rewrite -metric_real_power_cost_finite /metric_real_diameter_cost.
exact: metric_real_power_cost_monotone hc hp (metric_diameter_nonnegative (extended_metric_diameter_specification A)) hA.
Qed.

(** Source for [real_power_cutoff_finite_equal_diameter_cover]: supporting
    finite inner sum in the last display
    of 3.4.2(8), pp. 315–316. Every piece
    has the same finite diameter upper bound;
    neither nonemptiness nor measurable overlap is required. *)
Theorem real_power_cutoff_finite_equal_diameter_cover (R : realType) (X : metricType R)
    (I : finType) (c p : R) delta (nu : set X -> \bar R) A (S : I -> set X) (r : R) :
  @is_metric_scale_envelope R X (@nonempty_metric_sets R X)
    (fun j=>val j) (fun j=>metric_real_diameter_cost c p (val j)) delta nu ->
  (0<=c)%R -> (0<=p)%R -> (0<=r)%R -> r%:E<=delta ->
  (forall i, extended_metric_diameter (S i)<=r%:E) ->
  A `<=` \bigcup_i S i ->
    nu A<=(#|I|%:R*(c*real_power r p))%R%:E.
Proof.
move=> hn hc hp hr hcap hdiam hcover.
have hm : is_measure nu := metric_scale_envelope_is_measure hn
  (fun j=>metric_real_power_cost_nonnegative p (extended_metric_diameter (val j)) hc).
have hb := @measure_finite_indexed_cover R X I nu hm A S hcover.
have he : (\sum_(i : I) (c*real_power r p)%R%:E)=
    (#|I|%:R*(c*real_power r p))%R%:E.
  rewrite sumEFin sumr_const cardT; congr (_%:E); symmetry; exact: mulr_natl.
rewrite -he; apply: le_trans hb _; apply: lee_sum=> i _.
exact: real_power_cutoff_finite_diameter_bound hn hc hp hr hcap (hdiam i).
Qed.
