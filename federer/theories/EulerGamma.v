(** Public Euler Gamma interface, Federer (1969), 3.2.13,
    pp. 250–251. Exact graph laws and positive-domain
    evaluation use only the opaque independent specification. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal.
From Federer Require Import EulerGammaUP EulerGammaSealed PartialFunctionUP
  MeasureSubsetIntegral LebesgueScalarMeasure SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euler_gamma_graph]: the exact displayed
    defining Gamma integral, Federer 3.2.13, p. 250.
    There is no value outside the positive parameter domain. *)
Lemma euler_gamma_graph (R:realType) (s a:R):
  partial_function_graph (@EulerGamma.value R) s a <->
  (0<s)%R /\is_measure_subset_integral (@lebesgue_scalar_measure R) [set x:R|(0<x)%R]
    (real_total_integrand (euler_gamma_integrand s)) a%:E.
Proof. exact (@euler_gamma_graph_law R _ (@EulerGamma.laws R) s a). Qed.

(** Source for [euler_gamma]: evaluation of Gamma at
    a positive real parameter, Federer 3.2.13,
    pp. 250–251. The domain proof avoids assigning
    an artificial value at a nonpositive argument. *)
Definition euler_gamma (R:realType) (s:R) (hs:(0<s)%R):R:=
  projT1 (cid (euler_gamma_domain_law (@EulerGamma.laws R) hs)).

(** Source for [euler_gamma_value_graph]: the evaluated
    positive-domain value belongs to the abstract Gamma
    graph, Federer 3.2.13, p. 250. *)
Lemma euler_gamma_value_graph (R:realType) (s:R) (hs:(0<s)%R):
  partial_function_graph (@EulerGamma.value R) s (euler_gamma hs).
Proof. exact:projT2 (cid (euler_gamma_domain_law (@EulerGamma.laws R) hs)). Qed.

(** Source for [euler_gamma_positive]: positivity of every
    Gamma value used in the sphere and orthogonal
    projection formulas, Federer 3.2.13, pp. 250–251. *)
Lemma euler_gamma_positive (R:realType) (s:R) (hs:(0<s)%R):
  (0<euler_gamma hs)%R.
Proof. exact (@euler_gamma_positive_law R _ (@EulerGamma.laws R) s (euler_gamma hs) (euler_gamma_value_graph hs)). Qed.

(** Source for [euler_gamma_integral]: the defining
    positive-ray integral equals Gamma(s), Federer 3.2.13,
    p. 250, with actual finite integral existence. *)
Lemma euler_gamma_integral (R:realType) (s:R) (hs:(0<s)%R):
  is_measure_subset_integral (@lebesgue_scalar_measure R) [set x:R|(0<x)%R]
    (real_total_integrand (euler_gamma_integrand s)) (euler_gamma hs)%:E.
Proof. exact:((euler_gamma_graph s (euler_gamma hs)).1 (euler_gamma_value_graph hs)).2. Qed.
