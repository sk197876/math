(** Federer (1969), 3.2.19, p. 256: passage from a compact
    chart image to W when the omitted set has zero m-density.
    The approximate tangent is compared through its defining full-density
    test sets; no positive finite ball mass is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric MeasureUP MeasureRestriction
  PartialFunctionUP MetricDensities MetricDensityZeroUnions MeasureApproximateTangentUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measure_restrict_intersection]: supporting identity
    for the restricted measures used in Federer 3.2.19, p. 256,
    following the restriction definition of 2.1.2, p. 54. *)
Lemma measure_restrict_intersection (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (A B : set X) :
  measure_restrict (measure_restrict mu A) B=measure_restrict mu (A `&` B).
Proof. apply: funext=> C; by rewrite /measure_restrict setIA. Qed.

(** Source for [restricted_zero_density_enlarge]: the negligible
    omitted-chart set in Federer 3.2.19, p. 256. Adding it to
    a zero-density exceptional set leaves zero density. *)
Lemma restricted_zero_density_enlarge (R : realType) (X : metricType R) m
    (mu : set X -> \bar R) (A B Z : set X) a :
  is_measure mu ->
  partial_function_graph (metric_density m (measure_restrict mu (B `\` A))) a 0%E ->
  partial_function_graph (metric_density m (measure_restrict mu (A `&` Z))) a 0%E ->
  partial_function_graph (metric_density m (measure_restrict mu (B `&` Z))) a 0%E.
Proof.
move=> hm hLoss hAZ.
have hUnion := metric_restricted_density_zero_union hm hAZ hLoss.
apply: (metric_restricted_density_zero_subset hm _ hUnion)=> x [hxB hxZ].
case: (pselect (A x))=> hxA; [left|right]; by split.
Qed.

(** Source for [nested_restriction_zero_density_iff]: the full-density
    test sets for a chart image and W coincide when their difference
    has zero m-density, supporting Federer 3.2.19, p. 256. *)
Lemma nested_restriction_zero_density_iff (R : realType) (X : metricType R) m
    (mu : set X -> \bar R) (A B Z : set X) a :
  is_measure mu -> A `<=` B ->
  partial_function_graph (metric_density m (measure_restrict mu (B `\` A))) a 0%E ->
  (partial_function_graph (metric_density m (measure_restrict (measure_restrict mu A) Z)) a 0%E <->
   partial_function_graph (metric_density m (measure_restrict (measure_restrict mu B) Z)) a 0%E).
Proof.
move=> hm hAB hLoss; rewrite !measure_restrict_intersection; split.
- exact: restricted_zero_density_enlarge hm hLoss.
- apply: (metric_restricted_density_zero_subset hm _)=> x [hx hxZ]; split=> //; exact: hAB x hx.
Qed.

(** Source for [restricted_approximate_tangent_equal]: exact equality
    of the approximate tangent on the compact chart and on W in
    Federer 3.2.19, p. 256. The claim uses only zero omitted
    m-density and the independent intersection definition of 3.2.16. *)
Theorem restricted_approximate_tangent_equal (R : realType) (X : lmodType R)
    (NX : X -> R) (hNX : is_real_norm NX) m (mu : set X -> \bar R)
    (A B : set X) a :
  is_measure mu -> A `<=` B ->
  partial_function_graph (@metric_density R (real_norm_metric_space hNX) m
    (measure_restrict mu (B `\` A))) a 0%E ->
  measure_approximate_tangent_cone hNX (measure_restrict mu A) m a=
    measure_approximate_tangent_cone hNX (measure_restrict mu B) m a.
Proof.
move=> hm hAB hLoss.
have hTest S := @nested_restriction_zero_density_iff R (real_norm_metric_space hNX)
  m mu A B (~` S) a hm hAB hLoss.
apply/seteqP; split=> v hv S hS.
- exact: hv S ((hTest S).2 hS).
- exact: hv S ((hTest S).1 hS).
Qed.
