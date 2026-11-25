(** Federer (1969), 2.2.15, p. 71, final characterisation. We state the
    printed equivalence for a nonempty separable metric target. Under
    empty-space conventions the fully general equivalence includes an
    empty-target alternative; this local correction is not in Federer's
    erratum. See BaireEmptyTargetBoundary.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals topology.
From Federer Require Import RealMetricBackground BorelFunctionUP BaireFunctions
  FiniteCurveApproximationUP BaireTargetNecessity BaireTargetSufficiency BaireEmptyTargetBoundary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [borel_baire_target_criterion]: direct final
    equivalence in Federer 2.2.15, p. 71, for
    a nonempty separable metric target. All metric source spaces
    are allowed, with no completeness or separability assumption. *)
Theorem borel_baire_target_criterion (R : realType) (Y : metricType R)
    (y0 : Y) (D : set Y) : countable D -> dense D ->
  ((forall (X : metricType R) (f : X -> Y), is_borel_function f -> is_baire_function f) <->
    has_finite_curve_approximation Y).
Proof.
move=> hc hd; split.
- move=> h; apply: (@borel_baire_target_necessary R Y y0).
  exact: h [the metricType R of real_line_metric R].
- exact: borel_baire_target_sufficient hc hd.
Qed.

(** Source for [borel_baire_target_criterion_with_empty]: local
    boundary-complete version of Federer 2.2.15, p. 71.
    Empty targets satisfy the universal map assertion but cannot
    admit a real-parameter curve. Nonempty targets satisfy exactly
    the printed finite-curve condition. *)
Theorem borel_baire_target_criterion_with_empty (R : realType) (Y : metricType R)
    (D : set Y) : countable D -> dense D ->
  ((forall (X : metricType R) (f : X -> Y), is_borel_function f -> is_baire_function f) <->
    ((forall y : Y, False) \/ has_finite_curve_approximation Y)).
Proof.
move=> hc hd; split.
- move=> h; case: (pselect (exists y : Y, True))=> [[y0 _]|hn].
  + right; exact: (proj1 (@borel_baire_target_criterion R Y y0 D hc hd)) h.
  + left=> y; apply: hn; by exists y.
- move=> [he|h].
  + move=> X f hf; exact: empty_target_maps_baire he.
  + exact: borel_baire_target_sufficient hc hd h.
Qed.
