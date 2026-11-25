(** Federer (1969), 3.2.13, p. 250: Euler's
    Gamma function is specified by its actual defining
    integral on the positive real domain. Existence,
    finiteness and positivity are separate proof obligations. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import RealExponentialSealed RealPower RealMetricBackground
  PartialFunctionUP LebesgueScalarMeasure MeasureIntegralUP MeasureSubsetIntegral SummableRealFunctionUP
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euler_gamma_integrand]: exp(-x) x^(s-1)
    in the defining integral of Federer 3.2.13, p. 250.
    The defining subset integral uses only x>0. *)
Definition euler_gamma_integrand (R:realType) (s x:R):R:=
  (RealExponential.exponential (-x)*real_power x (s-1))%R.

(** Source for [is_euler_gamma]: the positive-domain
    defining integral of Euler Gamma in Federer 3.2.13,
    p. 250. Finite positive values and actual existence
    at every s>0 must be proved by an implementation;
    no project axiom or outside-domain default is introduced. *)
Record is_euler_gamma (R:realType)
    (G:partial_function R R):Prop:={
  (** Source for [euler_gamma_graph_law]: the displayed
      defining Gamma integral, Federer 3.2.13, p. 250. *)
  euler_gamma_graph_law:forall s a,partial_function_graph G s a <->
    (0<s)%R /\is_measure_subset_integral (@lebesgue_scalar_measure R) [set x|(0<x)%R]
      (real_total_integrand (euler_gamma_integrand s)) a%:E;
  (** Source for [euler_gamma_domain_law]: Gamma is
      defined at every positive s, Federer 3.2.13,
      p. 250; finiteness of the integral is an existence obligation. *)
  euler_gamma_domain_law:forall s,(0<s)%R ->exists a,partial_function_graph G s a;
  (** Source for [euler_gamma_positive_law]: positivity of
      the defining Gamma integral used as a divisor in
      Federer 3.2.13, pp. 250–251; derived during existence. *)
  euler_gamma_positive_law:forall s a,partial_function_graph G s a ->(0<a)%R
}.
