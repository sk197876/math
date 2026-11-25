(** Federer (1969), 4.1.2, p. 347: a
    measurable separable-target field with finite norm
    integral belongs to the original vector L1 domain.
    This adapter reuses the norm-integral and countable
    measurability theorems of 2.4.12 and 2.4.16. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric VectorDaniellHypotheses ExtendedRealOrderTopology PartialFunctionUP
  PartialFunctionBasic PartialNormPower RealPower MeasureUP MeasurableFunctionUP MeasurableGraphEquivalence
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralUniqueness SummableRealFunctionUP
  MeasureLoneNormIntegralGeneral MeasureLpNorm MeasureLpMembershipUP MeasureLpCountableMeasurability
  SeparableTargetNormedMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [total_vector_norm_power_one_graph]: the
    exponent-one norm integrand has exactly the finite
    values of the original vector norm, supporting
    Federer 4.1.2, p. 347, by 2.4.12, p. 86. *)
Lemma total_vector_norm_power_one_graph (R:realType) (X:Type) (Y:lmodType R)
    (N:Y->R) (hN:is_real_norm N) (f:X->Y) x y:
  partial_function_graph (partial_norm_power N 1
    (partial_function_total (fun x=>(f x:real_norm_metric_space hN)))) x y <->
  partial_function_graph (real_total_integrand (fun x=>N (f x))) x y.
Proof.
rewrite real_total_integrand_graph; split.
- move=>[v [hv hValue]]; change (f x=v) in hv.
  by rewrite -hv (@real_power_one_exponent R (N (f x)) (real_seminorm_nonnegative hN.1 (f x))) in hValue.
- move=>hValue; exists (f x); split; first reflexivity.
  by rewrite (@real_power_one_exponent R (N (f x)) (real_seminorm_nonnegative hN.1 (f x))).
Qed.

(** Source for [total_vector_norm_integrand_measurable]: the
    actual norm of a measurable vector field is
    measurable, supporting Federer 4.1.2, p. 347.
    The established norm-power theorem supplies this case. *)
Lemma total_vector_norm_integrand_measurable (R:realType) (X:choiceType) (Y:lmodType R)
    (N:Y->R) (hN:is_real_norm N) (mu:set X->\bar R) (hm:is_measure mu) (f:X->Y):
  is_measure_measurable_function mu (partial_function_total (fun x=>(f x:real_norm_metric_space hN))) ->
  is_measure_measurable_function mu (real_total_integrand (fun x=>N (f x))).
Proof.
move=>hf.
have h:=@measurable_lone_norm_integral R X Y N hN mu hm _ hf.
apply:(@measurable_function_graph_equivalent R X (extended_real_line R) mu _ _ _ h.1).
move=>x y; exact:(@total_vector_norm_power_one_graph R X Y N hN f x y).
Qed.

(** Source for [total_vector_lone_from_norm_integral]: finite
    norm integrability and separability give full original
    L1 membership, supporting the convolution integral in
    Federer 4.1.2, p. 347. No finite
    target dimension or finite ambient measure is added. *)
Theorem total_vector_lone_from_norm_integral (R:realType) (X:choiceType) (Y:lmodType R)
    (N:Y->R) (hN:is_real_norm N) (mu:set X->\bar R) (hm:is_measure mu) (f:X->Y) b:
  is_separable_normed_space hN ->
  is_measure_measurable_function mu (partial_function_total (fun x=>(f x:real_norm_metric_space hN))) ->
  is_measure_integral mu (real_total_integrand (fun x=>N (f x))) b%:E ->
  is_measure_lp_function mu 1 (partial_function_total (fun x=>(f x:real_norm_metric_space hN))).
Proof.
move=>[C [hCc hCd]] hf hIntegral.
have hNormed:=@separable_target_measurable_normed R X Y N hN C mu hm _ hCc hCd hf.
have hNorm:=@measurable_lone_norm_integral R X Y N hN mu hm _ hf.
have hPow:is_measure_integral mu
  (partial_norm_power N 1 (partial_function_total (fun x=>(f x:real_norm_metric_space hN)))) b%:E.
  apply:(@measure_integral_graph_equivalent R X mu _ _ b%:E _ hIntegral).
  move=>x y; symmetry; exact:(@total_vector_norm_power_one_graph R X Y N hN f x y).
have hEq:=measure_integral_unique hNorm hPow.
have hFinite:(measure_lp_norm mu N 1
    (partial_function_total (fun x=>(f x:real_norm_metric_space hN)))< +oo)%E.
  by rewrite hEq ltry.
split; first exact:lexx.
split; first exact hNormed.
split; first exact hFinite.
exact:(@finite_lp_norm_countably_measurable R X Y N hN mu hm 1 _ (lexx _) hf hFinite).
Qed.
