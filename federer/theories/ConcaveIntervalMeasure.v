(** Federer (1969), 2.10.28, pp. 191–193: the Caratheodory measure generated
    by compact intervals with concave diameter cost. Apply the existing
    opaque Caratheodory operator; prove its measure and regularity laws from
    the specifications alone. Singleton intervals are allowed and cost zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import RealMetricBackground MetricDiameter MetricDiameterReal CompactIntervalGauge
  ConcaveIntervalGaugeUP CaratheodoryLimitUP CaratheodoryMeasure MetricScaleEnvelopeUP
  NonnegativeSum NonnegativeSumSupport MeasureUP MeasureBasic TopologicalBorel BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [concave_interval_measure]: direct
    resulting measure psi in 2.10.28,
    p. 191, obtained through the existing
    sealed Caratheodory specification of 2.10.1. *)
Definition concave_interval_measure (R : realType) (h : R -> R) :=
  @caratheodory_measure R [the metricType R of real_line_metric R] (compact_real_intervals R)
    (fun j=>val j) (fun j=>(concave_interval_cost h (val j))%:E).

(** Source for [concave_interval_measure_specification]: direct
    diameter-restricted covering-limit laws for psi
    in 2.10.28, p. 191, from 2.10.1,
    p. 170, without assuming the later
    Cantor-set mass assertions. *)
Lemma concave_interval_measure_specification (R : realType) (h : R -> R) :
  is_caratheodory_limit (fun j : compact_real_intervals R=>val j)
    (fun j=>(concave_interval_cost h (val j))%:E) (concave_interval_measure h).
Proof. exact: caratheodory_measure_specification. Qed.

(** Source for [concave_interval_measure_is_measure]: supporting
    measure law for psi in 2.10.28,
    p. 191, by the nonnegative interval
    costs and the abstract laws of 2.10.1. *)
Lemma concave_interval_measure_is_measure (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) : is_measure (concave_interval_measure h).
Proof.
apply: caratheodory_measure_is_measure=> j; rewrite lee_fin.
exact (@concave_interval_cost_nonnegative R h hg (val j)).
Qed.

(** Source for [concave_interval_measure_borel_regular]: supporting
    Borel regularity of the interval-generated
    measure in 2.10.28, pp. 191–193,
    by closed generators and 2.10.1,
    p. 170. No special family is assumed. *)
Lemma concave_interval_measure_borel_regular (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) : is_borel_regular_measure (concave_interval_measure h).
Proof.
apply: caratheodory_measure_borel_regular.
- move=> j; rewrite lee_fin; exact (@concave_interval_cost_nonnegative R h hg (val j)).
- move=> j; apply: closed_borel_set; exact: compact_real_interval_closed (set_valP j).
Qed.

(** Source for [concave_interval_measure_singleton_zero]: supporting
    absence of atoms for the distribution function
    in 2.10.28, p. 193. The singleton
    itself belongs to F, has diameter zero
    and h(0)=0, and is admissible at
    every positive cutoff. *)
Lemma concave_interval_measure_singleton_zero (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (x : real_line_metric R) :
  concave_interval_measure h [set x]=0.
Proof.
have hm := concave_interval_measure_is_measure hg.
apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
pose I := compact_real_intervals R.
pose S := fun j : I=>val j.
pose c := fun j : I=>(concave_interval_cost h (val j))%:E.
have hJ : is_compact_real_interval (`[x,x] : set (real_line_metric R)).
  exists x,x; by split.
pose j : I := Sub (`[x,x] : set (real_line_metric R)) (mem_set hJ).
apply: (caratheodory_limit_least (concave_interval_measure_specification h))=> d nu hd hn.
have hdiam l : [set j] l -> extended_metric_diameter (S l)<=d.
  move=> ->; change (is_true (@extended_metric_diameter R [the metricType R of real_line_metric R] `[x,x]<=d)).
  rewrite (extended_metric_diameter_segment (lexx x)) subrr; exact: ltW hd.
have hcover : [set x] `<=` \bigcup_(l in [set j]) S l.
  have hx : (`[x,x] : set (real_line_metric R)) x by rewrite /= in_itv /= lexx.
  move=> y ->; exists j; first by [].
  exact hx.
have hh := @metric_scale_envelope_lower R [the metricType R of real_line_metric R] I S c d nu hn
  [set x] [set j] (countable1 j) hdiam hcover.
rewrite nonnegative_sum_singleton in hh; last first.
  rewrite /c lee_fin; exact (@concave_interval_cost_nonnegative R h hg (val j)).
by rewrite /c /= concave_interval_cost_segment // subrr (interval_gauge_zero hg) in hh.
Qed.
