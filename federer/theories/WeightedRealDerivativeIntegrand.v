(** Federer (1969), 2.9.21, p. 166: the integrands f g' and (f composed with
    g) g'. This public definition uses the existing abstract partial density
    product of 2.4.10; all its actual factors here are finite, while the
    domain remains exactly the derivative domain. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialDensityProduct
  SummableRealFunctionUP RealCurveDerivativeUP RealCurveDerivativeIntegrands.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [weighted_real_curve_derivative_integrand]: direct product f
    g' in Federer 2.9.21, p. 166 The finite total factor f is multiplied by
    the actual partial derivative integrand. No value is assigned when the
    derivative is undefined, even if f is zero there. *)
Definition weighted_real_curve_derivative_integrand (R : realType) (f g : R -> R) :=
  partial_density_product (real_total_integrand f) (real_curve_derivative_integrand g).

(** Source for [weighted_real_derivative_integrand_graph]: supporting exact
    graph convention for f g' in Federer 2.9.21, p. 166 Every actual value
    is the finite product of f(x) and the actual real derivative. *)
Lemma weighted_real_derivative_integrand_graph (R : realType) (f g : R -> R) x y :
  partial_function_graph (weighted_real_curve_derivative_integrand f g) x y <->
    exists v : R, has_real_curve_derivative g x v /\ (f x*v)%:E=y.
Proof.
rewrite /weighted_real_curve_derivative_integrand partial_density_product_graph; split.
- move=> [a [b [ha [[v [hv he]] hab]]]].
  have hfa := (real_total_integrand_graph f x a).1 ha.
  exists v; split=> //; by rewrite -hfa -he -EFinM in hab.
- move=> [v [hv he]]; exists (f x)%:E,v%:E; split.
  + by apply/real_total_integrand_graph.
  + split; first by exists v; split.
    by rewrite -EFinM.
Qed.
