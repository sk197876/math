(** Federer (1969), 2.9.22, p. 168: actual finite integrals of the norm
    distance N(v(t)-z) on bounded intervals. This supporting lemma applies
    finite-restriction integrability to the translated vector field. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormClosureLaws ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension MeasureUP MeasureSubsetIntegral
  MeasurableFunctionUP MeasurableTotalBasic BorelFunctionBasic SummableRealFunctionUP
  MeasureIntegralGraphEquivalence MeasurableDistanceTo BoundedVectorNormSubsetIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [total_norm_distance_graph]: supporting
    exact integrand graph in Federer 2.9.22, p. 168,
    the norm-error display. For a total vector field,
    distance to z is precisely the finite embedding of N(v(t)-z). *)
Lemma total_norm_distance_graph (R : realType) (X : Type) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N)
    (v : X -> real_norm_metric_space hN) (z : real_norm_metric_space hN) x y :
  partial_function_graph (partial_distance_to (partial_function_total v) z) x y <->
  (N (v x-z))%:E=y.
Proof.
split.
- by move=> [w [hw he]]; rewrite -(hw : v x=w) real_norm_metric_distanceE in he.
- move=> he; exists (v x); by split.
Qed.

(** Source for [bounded_vector_distance_subset_integral]:
    supporting finite distance integral in Federer 2.9.22,
    p. 168, using 2.4.12 on a finite-measure restriction.
    Translation preserves measurability and gives the bound
    N(v(t)-z)<=L+N(z); no global L1 assumption is added. *)
Lemma bounded_vector_distance_subset_integral (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (C : set (real_norm_metric_space hN)) (mu : set X -> \bar R)
    (hm : is_measure mu) (A : set X) (m L : R)
    (v : X -> real_norm_metric_space hN) (z : real_norm_metric_space hN) :
  countable C -> dense C -> measure_measurable mu A -> mu A=m%:E ->
  is_measure_measurable_function mu (partial_function_total v) ->
  (forall x, N (v x)<=L) -> exists J : R,
  is_measure_subset_integral mu A (partial_distance_to (partial_function_total v) z) J%:E.
Proof.
move=> hCc hCd hA hmass hv hb.
pose w x : real_norm_metric_space hN := v x-z.
have hc : continuous (fun y : real_norm_metric_space hN => (y-z : real_norm_metric_space hN)).
  have he : (fun y : real_norm_metric_space hN => y-z)=(fun y => -z+y).
    by apply/funext=> y; rewrite addrC.
  rewrite he; exact: real_norm_metric_translate_continuous.
have hw : is_measure_measurable_function mu (partial_function_total w).
  exact (@measurable_total_borel_postcomposition R X
    [the topologicalType of real_norm_metric_space hN]
    [the topologicalType of real_norm_metric_space hN] mu hm v
    (fun y => y-z) hv (continuous_borel_function hc)).
have hbound x : N (w x)<=L+N z.
  have ht := real_seminorm_triangle hN.1 (v x) (-z).
  rewrite (real_seminorm_negate hN.1) in ht.
  exact: le_trans ht (lerD (hb x) (lexx _)).
have [J hJ] := @bounded_vector_norm_subset_integral R X E N hN C mu hm A m (L+N z) w
  hCc hCd hA hmass hw hbound.
exists J; apply: (@measure_integral_graph_equivalent R X mu _ _ J%:E _ hJ)=> x y.
rewrite !partial_function_zero_extension_graph; split.
- move=> [[hx he]|hx]; last by right.
  left; split=> //; apply/total_norm_distance_graph.
  exact: (real_total_integrand_graph _ _ _).1 he.
- move=> [[hx he]|hx]; last by right.
  left; split=> //; apply/real_total_integrand_graph.
  exact: (total_norm_distance_graph _ _ _ _).1 he.
Qed.
