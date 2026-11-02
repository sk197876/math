(** Federer (1969), 2.9.22, pp. 167–168: the integral of the norm of the
    actual vector derivative extends the final bound in 2.9.19, pp. 164–165.
    The derivative remains a partial function; its norm is embedded in the
    project's scalar integral carrier. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal topology.
From Federer Require Import RealNormUP NormedCurveDerivativeUP PartialFunctionUP
  PartialFunctionPostcomposition ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [normed_curve_norm_derivative_integrand]: direct
    norm integrand in the extension asserted by Federer 2.9.22,
    pp. 167–168, of the integral bound in 2.9.19, p. 165.
    Postcomposition changes only the values, preserving exactly the
    domain where the actual two-sided vector norm derivative exists. *)
Definition normed_curve_norm_derivative_integrand (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> E) :=
  partial_function_postcompose (normed_curve_derivative hN g)
    (fun v => (N v)%:E : extended_real_line R).

(** Source for [normed_curve_norm_derivative_integrand_graph]:
    supporting exact integrand graph for Federer 2.9.22,
    pp. 167–168, extending 2.9.19, p. 165. Every value is
    the finite norm of an actual derivative; no value is supplied
    at a nondifferentiability point. *)
Lemma normed_curve_norm_derivative_integrand_graph (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> E) x y :
  partial_function_graph (normed_curve_norm_derivative_integrand hN g) x y <->
    exists v : E, has_normed_curve_derivative N g x v /\ (N v)%:E=y.
Proof. by []. Qed.

(** Source for [normed_curve_norm_derivative_nonnegative]: supporting
    positivity of the actual norm integrand in Federer 2.9.22,
    pp. 167–168, extending 2.9.19, p. 165. Every graph value
    is nonnegative solely by the supplied norm laws. *)
Lemma normed_curve_norm_derivative_nonnegative (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> E) x y :
  partial_function_graph (normed_curve_norm_derivative_integrand hN g) x y -> (0<=y)%E.
Proof. by move=> [v [_ <-]]; rewrite lee_fin (real_seminorm_nonnegative hN.1). Qed.
