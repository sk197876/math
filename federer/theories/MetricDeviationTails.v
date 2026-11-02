(** Federer (1969), 2.3.7, pp. 77–78: the decreasing tail deviation sets
    C_{i,j}. Source context: UniformPartialConvergenceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionLimitUP MeasureUP
  MeasureCountableClosure MeasurableFunctionUP MeasurableMetricDistance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [partial_metric_deviation_tail]: direct C_{i,j}
    of Federer 2.3.7, p. 77, with the distance threshold
    exposed as eta and natural indices starting at zero. *)
Definition partial_metric_deviation_tail (R : realType) (X : Type)
    (Y : metricType R) (f : nat -> partial_function X Y) (g : partial_function X Y)
    (eta : R) N : set X :=
  \bigcup_(n in [set n | (N <= n)%N]) partial_metric_deviation_set (f n) g eta.

(** Source for [partial_metric_deviation_tail_measurable]: the measurability
    of C_{i,j} used in Federer 2.3.7, pp. 77–78 *)
Lemma partial_metric_deviation_tail_measurable (R : realType) (X : choiceType)
    (Y : metricType R) (mu : set X -> \bar R) (hm : is_measure mu)
    (D : set Y) (f : nat -> partial_function X Y) (g : partial_function X Y) eta N :
  countable D -> dense D -> (forall n, is_measure_measurable_function mu (f n)) ->
  is_measure_measurable_function mu g -> measure_measurable mu (partial_metric_deviation_tail f g eta N).
Proof.
move=> hc hd hf hg.
apply: (@measure_measurable_countable_union R X nat mu hm _ _ (countableP _))=> n hn.
exact (@partial_metric_deviation_measurable R X Y mu hm D (f n) g eta hc hd (hf n) hg).
Qed.

(** Source for [partial_metric_deviation_tail_antitone]: supporting
    decreasing property of C_{i,j} as j increases in Federer
    2.3.7, p. 78, first display. *)
Lemma partial_metric_deviation_tail_antitone (R : realType) (X : Type)
    (Y : metricType R) (f : nat -> partial_function X Y) (g : partial_function X Y) eta N M :
  (N <= M)%N -> partial_metric_deviation_tail f g eta M `<=`
    partial_metric_deviation_tail f g eta N.
Proof. move=> hNM x [n hn hx]; exists n=> //; exact: leq_trans hNM hn. Qed.

(** Source for [partial_metric_limit_avoids_tail_intersection]:
    supporting vanishing of the limiting exceptional set in
    Federer 2.3.7, p. 78. At a convergent point every fixed
    positive threshold is eventually avoided. *)
Lemma partial_metric_limit_avoids_tail_intersection (R : realType) (X : Type)
    (Y : metricType R) (f : nat -> partial_function X Y) (g : partial_function X Y) eta :
  0 < eta -> (\bigcap_N partial_metric_deviation_tail f g eta N) `<=`
    ~` partial_function_limit_locus f g.
Proof.
move=> he x hx [u [z [hu [hz hlim]]]].
have hnb : nbhs z [set y | mdist z y < eta].
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP z _)); exists eta=> // y hy; exact hy.
have [N _ hN] := hlim _ hnb.
have [n hn [y [w [hy [hw hbad]]]]] := hx N Logic.I.
have hyu := @partial_function_single_valued X Y (f n) x y (u n) hy (hu n).
have hwz := @partial_function_single_valued X Y g x w z hw hz.
rewrite hyu hwz in hbad.
have hgood : mdist z (u n) < eta := hN n hn.
rewrite metric_sym in hgood.
by have := le_lt_trans hbad hgood; rewrite ltxx.
Qed.
