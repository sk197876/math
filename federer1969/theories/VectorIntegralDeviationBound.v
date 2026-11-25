(** Federer (1969), 2.9.22, p. 168, norm-error display: the norm of the
    integral of v(t)-v(x) is bounded by the integral of its norm. This
    consequence is proved from the abstract vector-integral laws of 2.4.12,
    pp. 87–88. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealOrderTopology PartialFunctionUP
  PartialFunctionBasic PartialNormedArithmetic PartialNormPower RealPower
  MeasureUP MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  MeasureVectorIntegralUP MeasureVectorIntegralDifference MeasureVectorIntegralBound
  MeasureLoneNormIntegral MeasureLpNorm MeasureLpConvergence SummableRealFunctionUP
  FiniteMeasureVectorConstant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [total_vector_difference_norm_graph]: supporting
    exact norm integrand for the error display in Federer
    2.9.22, p. 168. At exponent one, the norm power
    of the pointwise vector difference is exactly the finite
    real embedding of N(v(t)-z). *)
Lemma total_vector_difference_norm_graph (R : realType) (X : Type)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (v : X -> real_norm_metric_space hN) (z : E) x y :
  partial_function_graph
    (partial_norm_power N 1 (partial_vector_subtract (partial_function_total v)
      (partial_function_total (fun _ : X => (z : real_norm_metric_space hN))))) x y <->
  (N (v x-z))%:E=y.
Proof.
split.
- move=> [w [hw he]].
  have [p [q [hp [hq hw']]]] := (partial_vector_subtract_graph _ _ _ _).1 hw.
  rewrite hw' -(hp : v x=p) -(hq : z=q) in he.
  rewrite (@real_power_one_exponent R (N (v x-z))
    (real_seminorm_nonnegative hN.1 _)) in he.
  exact he.
- move=> he; exists (v x-z); split.
    apply/partial_vector_subtract_graph; exists (v x),z; by split=> //; split.
  by rewrite (@real_power_one_exponent R (N (v x-z))
    (real_seminorm_nonnegative hN.1 _)).
Qed.

(** Source for [vector_integral_deviation_bound]: direct
    supporting norm-error bound of Federer 2.9.22, p. 168.
    For a finite measure of mass m and actual integral y
    of v, N(y-m z) is at most the actual norm-deviation
    integral. The latter may be infinite; no undefined
    subtraction or default integral value is used. *)
Theorem vector_integral_deviation_bound (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (m : R)
    (v : X -> real_norm_metric_space hN) (y z : E) (J : \bar R) :
  mu setT=m%:E -> is_measure_vector_integral mu (partial_function_total v) y ->
  is_measure_integral mu (real_total_integrand (fun x => N (v x-z))) J ->
  ((N (y-m *: z))%:E<=J)%E.
Proof.
move=> hmass hv hJ.
have hz := @finite_measure_vector_constant_integral R X E N hN mu hm m z hmass.
have hd := @measure_vector_integral_subtract R X E N hN mu hm _ _ y (m *: z) hv hz.
have hn := @measure_lone_norm_integral R X E N hN mu hm _ hd.1.
have hi : is_measure_integral mu (real_total_integrand (fun x => N (v x-z)))
    (measure_lp_norm mu N 1
      (partial_vector_subtract (partial_function_total v)
        (partial_function_total (fun _ : X => (z : real_norm_metric_space hN))))).
  apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hn)=> x t.
  by rewrite total_vector_difference_norm_graph real_total_integrand_graph.
have he := measure_integral_unique hi hJ.
have hb := @measure_vector_integral_norm_bound R X E N hN mu hm _ _ hd.
by rewrite he in hb.
Qed.
