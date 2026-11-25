(** Federer (1969), 2.3.5, pp. 76–77, metric-space case of Lusin's theorem.
    The local LaTeX erratum contains no mathematical correction to this
    theorem. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialContinuityUP MeasureUP
  MeasurableFunctionUP BorelRegularMeasureUP BorelRegularApproximation
  TopologicalBorel LusinClosedApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lusin_borel_regular]: direct metric case of Federer 2.3.5,
    pp. 76–77. The separability hypothesis is expressed by a countable dense
    subset. The closed set lies in A and the partial function's domain; the
    latter is part of the continuity specification and explicit. *)
Theorem lusin_borel_regular (R : realType) (X Y : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (hr : is_borel_regular_measure mu) (D : set Y) (A : set X)
    (f : partial_function X Y) (epsilon : R) : countable D -> dense D ->
  is_measure_measurable_function mu f -> measure_measurable mu A -> mu A < +oo ->
  (0 < epsilon)%R -> exists C, closed C /\ C `<=` A /\
    mu (A `\` C) < epsilon%:E /\ partial_function_continuous_on C f.
Proof.
move=> hc hd hf hA hfin he.
apply: (@lusin_closed_approximation R X Y mu hm D A f epsilon hc hd _ _ hf hA hfin he).
- move=> K hK; apply: (@borel_regular_borel_measurable R X mu hm hr K).
  exact: closed_borel_set hK.
- move=> H hH hfinH; exact: (@borel_regular_closed_approximation R X mu hm hr H hH hfinH).
Qed.
