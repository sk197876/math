(** Federer (1969), 2.2.15, p. 71, final criterion: local boundary
    clarification under the project's convention allowing empty metric
    spaces. Every map into an empty target is continuous, hence Baire, but
    the printed curve condition for the empty finite set requires a map from
    R into that empty target and is impossible. The criterion therefore
    needs a nonempty target, or an explicit empty-target alternative. This
    is a local correction, not an entry in Federer's erratum; the working
    transcription has no relevant correction on pp. 70–71. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import RealMetricBackground MetricSubsetBackground BaireFunctions
  BorelFunctionUP FiniteCurveApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [empty_target_maps_continuous]: supporting
    empty-target counterexample to the unqualified final criterion
    in Federer 2.2.15, p. 71. A map into an
    empty space has no source points at which continuity could fail. *)
Lemma empty_target_maps_continuous (X Y : topologicalType) (f : X -> Y) :
  (forall y : Y, False) -> continuous f.
Proof. move=> he x; exfalso; exact: he (f x). Qed.

(** Source for [empty_target_maps_baire]: local boundary
    fact for Federer 2.2.15, p. 71: every map
    into an empty metric target is Baire, so the universal
    Borel-to-Baire assertion is true for that target. *)
Lemma empty_target_maps_baire (R : realType) (X : topologicalType) (Y : metricType R)
    (f : X -> Y) : (forall y : Y, False) -> is_baire_function f.
Proof. move=> he; apply: continuous_baire_function; exact: empty_target_maps_continuous he. Qed.

(** Source for [empty_target_curve_approximation_impossible]: local
    counterexample to the printed curve condition in Federer
    2.2.15, p. 71. Applying it to the empty finite
    set and epsilon one still demands a curve, whose value
    at zero would be an element of the empty target. *)
Lemma empty_target_curve_approximation_impossible (R : realType) (Y : metricType R) :
  (forall y : Y, False) -> ~ has_finite_curve_approximation Y.
Proof.
move=> he hc.
have hf : finite_set (@set0 Y) := finite_set0 Y.
have [c _] := hc set0 hf 1 (@ltr01 R).
exact: he (c 0).
Qed.

(** Source for [empty_target_borel_baire_counterexample]: explicit
    local empty-space counterexample to the unqualified final iff
    in Federer 2.2.15, p. 71. The target is a
    separable metric space; every Borel map into it is Baire,
    while its finite-curve condition is false. This is kept
    separate from the nonempty-target theorem and Federer's erratum. *)
Theorem empty_target_borel_baire_counterexample (R : realType) :
  exists Y : metricType R,
    (exists D : set Y, countable D /\ dense D) /\
    (forall (X : metricType R) (f : X -> Y), is_borel_function f -> is_baire_function f) /\
    ~ has_finite_curve_approximation Y.
Proof.
pose Y := [the metricType R of metric_subset (@set0 [the metricType R of real_line_metric R])].
have he (y : Y) : False := set_valP y.
exists Y; split.
- exists set0; split; first exact: finite_set_countable (@finite_set0 Y).
  move=> V [y hy] ho; exact: False_ind _ (he y).
- split.
  + move=> X f hf; exact: empty_target_maps_baire he.
  + exact: empty_target_curve_approximation_impossible he.
Qed.
