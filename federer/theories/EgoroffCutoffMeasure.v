(** Federer (1969), 2.3.7, p. 78: the exceptional-set union has small
    measure. Source context: UniformPartialConvergenceUP.v. We keep A
    arbitrary and estimate its intersections with the chosen tails, using
    the locally proved summable-error bound. The required summands are the
    measures of A intersected with those tails, as established before that
    display. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureUP MeasureBasic MeasureSplit MeasureAlmostBasic
  MeasureFiniteClosure MeasureCountableClosure MeasurableFunctionUP MetricDeviationTails
  PartialSequenceCommonDomain EgoroffThresholds EgoroffCutoffSet GeometricErrorBudget MeasureGeometricCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [egoroff_cutoff_measurable]: direct measurability of B in
    Federer 2.3.7, p. 78, with the common domain made explicit. *)
Lemma egoroff_cutoff_measurable (R : realType) (X : choiceType) (Y : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu) (D : set Y)
    (f : nat -> partial_function X Y) (g : partial_function X Y) (J : nat -> nat) :
  countable D -> dense D -> (forall n, is_measure_measurable_function mu (f n)) ->
  is_measure_measurable_function mu g -> measure_measurable mu (egoroff_cutoff_set f g J).
Proof.
move=> hc hd hf hg; apply: (@measure_measurable_difference R X mu hm).
- exact: (@partial_sequence_common_domain_measurable R X Y mu hm f g hf hg).
- apply: (@measure_measurable_sequence_union R X mu hm)=> i.
  exact: (@partial_metric_deviation_tail_measurable R X Y mu hm D f g _ _ hc hd hf hg).
Qed.

(** Source for [egoroff_cutoff_error]: direct error bound in
    Federer 2.3.7, p. 78. Half-error geometric budgets ensure
    the strict inequality even after countable subadditivity.
    Only A intersected with each exceptional tail is measured. *)
Lemma egoroff_cutoff_error (R : realType) (X : choiceType) (Y : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (f : nat -> partial_function X Y) (g : partial_function X Y) (J : nat -> nat) (e : R) :
  (forall n, is_measure_measurable_function mu (f n)) -> is_measure_measurable_function mu g ->
  (0 < e)%R -> (forall i, mu (A `&` partial_metric_deviation_tail f g (egoroff_threshold i) (J i))
    < (geometric_error_budget e i)%:E) -> mu (A `\` egoroff_cutoff_set f g J) < e%:E.
Proof.
move=> hf hg he hJ.
pose T i := partial_metric_deviation_tail f g (egoroff_threshold i) (J i).
pose E := A `&` \bigcup_i T i.
have hE : mu E < e%:E.
  apply: (proj2 (@measure_geometric_cover_bound R X mu hm E (fun i => A `&` T i) e he _ hJ)).
  move=> x [ha [i _ hx]]; exists i; first exact Logic.I; by split.
have hnull : mu (A `\` partial_sequence_common_domain f g) = 0.
  apply: (@measure_null_subset R X mu hm _ (~` partial_sequence_common_domain f g)).
  - by move=> x [_ hx].
  - exact: (@partial_sequence_common_domain_conull R X Y mu hm f g hf hg).
have hcover : (A `\` egoroff_cutoff_set f g J) `<=`
    (A `\` partial_sequence_common_domain f g) `|` E.
  move=> x [ha hn]; case: (pselect (partial_sequence_common_domain f g x))=> hx; last by left; split.
  right; split=> //; apply: contrapT=> hnone; apply: hn; by split.
have hb := @measure_binary_cover R X mu hm _ _ _ hcover.
rewrite hnull add0e in hb; exact: le_lt_trans hb hE.
Qed.
