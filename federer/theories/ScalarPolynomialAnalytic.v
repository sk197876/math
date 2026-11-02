(** Federer (1969), 3.1.24, p. 240: scalar
    polynomial maps in the explicit inverse majorant are analytic,
    using the project's intrinsic polynomial-function interface. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP SymmetricForms
  SymmetricFormSum PolynomialFunctions PolynomialRepresentations ScalarSymmetricFormBound
  NormAnalyticUP NormAnalyticPolynomial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_polynomial_function_analytic]: supporting
    the affine and quadratic expressions in Federer 3.1.24,
    p. 240. Every polynomial from the scalar line to
    a Banach space is analytic; multilinearity proves the
    coefficient continuity without an extra hypothesis. *)
Theorem scalar_polynomial_function_analytic (R:realType) (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY)
    (hcomplete:is_complete_metric_space (real_norm_metric_space hNY))
    (P:PolynomialFunction R^o Y) :
  @norm_analytic R R^o Y (fun t=>`|t|) NY (scalar_absolute_value_norm R) hNY setT P.
Proof.
apply:(@norm_polynomial_function_analytic R R^o Y (fun t=>`|t|) NY
  (scalar_absolute_value_norm R) hNY hcomplete P)=>i hi.
exact (scalar_symmetric_form_bound hNY.1 _).
Qed.
