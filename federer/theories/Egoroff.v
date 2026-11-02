(** Federer (1969), 2.3.7, pp. 77–78, Egoroff's theorem. A need not be
    measurable and B need not be a subset of A. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionLimitUP UniformPartialConvergenceUP
  MeasureUP MeasureAlmostUP MeasurableFunctionUP MetricDeviationTails MeasureDeviationTail
  EgoroffThresholds EgoroffCutoffSet EgoroffCutoffMeasure GeometricErrorBudget.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [egoroff_measurable_partial_functions]: direct
    Federer 2.3.7, pp. 77–78. Almost-everywhere convergence
    on an arbitrary finite-measure A becomes uniform on a measurable
    B with arbitrarily small measure of A minus B. *)
Theorem egoroff_measurable_partial_functions (R : realType) (X : choiceType)
    (Y : metricType R) (mu : set X -> \bar R) (hm : is_measure mu)
    (D : set Y) (A : set X) (f : nat -> partial_function X Y)
    (g : partial_function X Y) (e : R) : countable D -> dense D ->
  (forall n, is_measure_measurable_function mu (f n)) -> is_measure_measurable_function mu g ->
  mu A < +oo -> measure_almost_everywhere_on mu A (partial_function_limit_locus f g) ->
  (0 < e)%R -> exists B, measure_measurable mu B /\ mu (A `\` B) < e%:E /\
    partial_function_uniformly_converges_on B f g.
Proof.
move=> hc hd hf hg hfin hlim he.
have hex i := @measure_deviation_tail_small R X Y mu hm D A f g
  (egoroff_threshold i) (geometric_error_budget e i) hc hd hf hg hfin hlim
  (@egoroff_threshold_positive R i) (geometric_error_budget_positive i he).
pose J i := projT1 (cid (hex i)).
have hJ i : mu (A `&` partial_metric_deviation_tail f g (egoroff_threshold i) (J i))
    < (geometric_error_budget e i)%:E.
  exact: projT2 (cid (hex i)).
exists (egoroff_cutoff_set f g J); split.
- exact (@egoroff_cutoff_measurable R X Y mu hm D f g J hc hd hf hg).
- split; first exact (@egoroff_cutoff_error R X Y mu hm A f g J e hf hg he hJ).
  exact: egoroff_cutoff_uniform.
Qed.
