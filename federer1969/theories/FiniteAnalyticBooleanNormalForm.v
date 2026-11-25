(** Federer (1969), 3.4.5, p. 321: finite
    Boolean operations on original analytic subvarieties yield
    exactly finite unions of differences of those varieties. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric FiniteAnalyticVarietyUP FiniteAnalyticVarietyLaws
  FiniteAnalyticVarietyBoundary FiniteBooleanDifferenceUP FiniteBooleanDifferenceNormal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_analytic_boolean_normal_form]: the
    exact class displayed as a finite union of S_i minus
    T_i in 3.4.5, p. 321. All S_i
    and T_i are actual finite analytic subvarieties of the
    same original U; no additional measurability or
    finiteness premise is introduced. *)
Theorem finite_analytic_boolean_normal_form (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (U S:set X):
  @open (real_norm_metric_space hNX) U ->
  (finite_boolean_set_closure (@is_finite_analytic_variety R X NX hNX U) S <->
    has_finite_difference_form (@is_finite_analytic_variety R X NX hNX U) S).
Proof.
move=>hU.
exact:(@finite_boolean_difference_normal_form [the choiceType of (X:Type)] U
  (@is_finite_analytic_variety R X NX hNX U)
  (@finite_analytic_variety_domain_empty R X NX hNX U hU)
  (@finite_analytic_variety_domain_whole R X NX hNX U hU)
  (@finite_analytic_variety_union R X NX hNX U)
  (@finite_analytic_variety_intersection R X NX hNX U)
  (@finite_analytic_variety_domain_inside R X NX hNX U) S).
Qed.
