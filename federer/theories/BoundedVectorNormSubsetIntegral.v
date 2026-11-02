(** Federer (1969), 2.9.22, pp. 167–168: local norm integrability of the
    bounded measurable derivative field, needed for the Lebesgue-point
    theorem 2.9.9, pp. 156–157. This supporting lemma uses full L1
    membership after finite-measure restriction, then the existing integral
    specification. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition PartialNormPower RealPower
  MeasureUP MeasureRestriction MeasureIntegralUP MeasureSubsetIntegral MeasurableFunctionUP
  MeasureLpNorm MeasureLpMembershipUP MeasureLoneNormIntegral MeasureIntegralGraphEquivalence
  RestrictedIntegralIdentity SummableRealFunctionUP BoundedRestrictedVectorIntegrability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bounded_vector_norm_subset_integral]: supporting
    finite local integral of N(v) in Federer 2.9.22,
    pp. 167–168, before applying 2.9.9. The result
    gives an actual finite subset integral on each measurable
    finite-measure set. No global L1 hypothesis is imposed. *)
Lemma bounded_vector_norm_subset_integral (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (C : set (real_norm_metric_space hN)) (mu : set X -> \bar R)
    (hm : is_measure mu) (A : set X) (m L : R)
    (v : X -> real_norm_metric_space hN) :
  countable C -> dense C -> measure_measurable mu A -> mu A=m%:E ->
  is_measure_measurable_function mu (partial_function_total v) ->
  (forall x, N (v x)<=L) ->
  exists J : R, is_measure_subset_integral mu A (real_total_integrand (fun x => N (v x))) J%:E.
Proof.
move=> hCc hCd hA hmass hv hb.
have hf := @bounded_restricted_vector_lone R X E N hN C mu hm A m L v hCc hCd hmass hv hb.
have hmA := measure_restrict_is_measure hm A.
have hn := @measure_lone_norm_integral R X E N hN (measure_restrict mu A) hmA
  (partial_function_total v) hf.
pose q := measure_lp_norm (measure_restrict mu A) N 1 (partial_function_total v).
have hq0 := @measure_lp_norm_nonnegative R X E N hN (measure_restrict mu A)
  1 (partial_function_total v) hmA (lexx _) hf.2.1.1.
have hqf : q \is a fin_num.
  rewrite /q (ge0_fin_numE hq0); exact: hf.2.2.1.
have hi : is_measure_integral (measure_restrict mu A)
    (real_total_integrand (fun x => N (v x))) q.
  apply: (@measure_integral_graph_equivalent R X (measure_restrict mu A) _ _ _ _ hn)=> x y.
  rewrite real_total_integrand_graph; split.
  - move=> [z [hz he]].
    rewrite -(hz : v x=z)
      (@real_power_one_exponent R (N (v x)) (real_seminorm_nonnegative hN.1 _)) in he.
    exact he.
  - move=> he; exists (v x); split=> //.
    by rewrite (@real_power_one_exponent R (N (v x)) (real_seminorm_nonnegative hN.1 _)).
exists (fine q).
apply: (@restricted_integral_zero_extension_iff R X mu hm A _ _ hA).1.
by rewrite fineK.
Qed.
