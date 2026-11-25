(** Federer (1969), 2.9.19, pp. 163–165: use the actual finite partial
    derivative as an integrand, and integrate its absolute value. These
    adapters retain the derivative's exact domain; no derivative value is
    assigned on its exceptional set. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealCurveDerivativeUP PartialFunctionUP PartialFunctionPostcomposition
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_curve_derivative_integrand]: direct real derivative g'
    of Federer 2.9.19, pp. 163–165, viewed in the extended-real integrand
    convention of 2.4.2, p. 81. Only the range is embedded; the partial
    domain remains exactly the derivative domain. *)
Definition real_curve_derivative_integrand (R : realType) (g : R -> R) :=
  partial_function_postcompose (real_curve_derivative g)
    (fun v => (v%:E : extended_real_line R)).

(** Source for [real_curve_absolute_derivative_integrand]: direct |g'| in
    the final integral of Federer 2.9.19, pp. 164–165 Apply the absolute
    value to actual derivative values and embed the finite result as an
    integrand. *)
Definition real_curve_absolute_derivative_integrand (R : realType) (g : R -> R) :=
  partial_function_postcompose (real_curve_derivative g)
    (fun v => (`|v|%:E : extended_real_line R)).

(** Source for [real_curve_derivative_integrand_graph]: supporting graph
    convention for g' in Federer 2.9.19, pp. 163–165 Every graph value is
    the finite embedding of the actual derivative. *)
Lemma real_curve_derivative_integrand_graph (R : realType) (g : R -> R) x y :
  partial_function_graph (real_curve_derivative_integrand g) x y <->
    exists v : R, has_real_curve_derivative g x v /\ v%:E=y.
Proof. by []. Qed.

(** Source for [real_curve_absolute_derivative_integrand_graph]: supporting
    exact graph for the final integral in Federer 2.9.19, pp. 164–165 No
    graph value exists unless g is differentiable at x, and that value is
    the finite |g'(x)|. *)
Lemma real_curve_absolute_derivative_integrand_graph (R : realType) (g : R -> R) x y :
  partial_function_graph (real_curve_absolute_derivative_integrand g) x y <->
    exists v : R, has_real_curve_derivative g x v /\ `|v|%:E=y.
Proof. by []. Qed.

(** Source for [real_curve_absolute_derivative_nonnegative]: supporting sign
    of |g'| in Federer 2.9.19, pp. 164–165 Every actual graph value is
    nonnegative, independently of any measure or almost-everywhere existence
    theorem. *)
Lemma real_curve_absolute_derivative_nonnegative (R : realType) (g : R -> R) x y :
  partial_function_graph (real_curve_absolute_derivative_integrand g) x y -> (0<=y)%E.
Proof. by move=> [v [_ <-]]; rewrite lee_fin normr_ge0. Qed.
