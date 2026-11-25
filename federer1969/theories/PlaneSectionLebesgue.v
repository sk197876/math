(** Federer (1969), 2.5.4, pp. 95-96: in example (1), "lambda_1(u o p) =
    int_0^1 u dL^1" for continuous u : R -> R, and in example (2),
    "lambda_2(f) = int_0^1 f(t, 0) dL^1 t" for continuous real valued f on
    R^2. In PlaneRegularMeasureExamples.v both functionals are the Riemann
    integral [plane_section_integral] F |-> int_0^1 F(t, 0) dt of 2.5.17.
    This module identifies that Riemann integral with the integral over {t :
    0 <= t <= 1} with respect to the sealed one dimensional Lebesgue measure
    L^1 of 2.5.17, p. 111, by [lebesgue_riemann_continuous_segment]. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground SummableRealFunctionUP MeasureIntegralUP
  MeasureSubsetIntegral StieltjesSums StieltjesIntegral LebesgueScalarMeasure
  LebesgueRiemannContinuous PlaneRegularMeasureExamples.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PlaneSectionLebesgue.
Variable R : realType.

(** Source for [plane_section_integral_lebesgue]: "lambda_2(f) =
    int_0^1 f(t, 0) dL^1 t" for f in L_2, Federer 2.5.4(2), p. 96. Direct
    formalisation: the Riemann integral [plane_section_integral] is the
    integral of t |-> f(t, 0) over {t : 0 <= t <= 1} with respect to
    L^1. *)
Theorem plane_section_integral_lebesgue (F : (R * R)%type -> R) :
  plane_continuous_lattice F ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[0, 1]
    (real_total_integrand (fun t => F (t, 0))) (plane_section_integral F)%:E.
Proof.
move=> hF.
exact: (lebesgue_riemann_continuous_segment (plane_continuous_lattice_section hF) ltr01).
Qed.

(** Source for [first_coordinate_integral_lebesgue]: "lambda_1(u o p) =
    int_0^1 u dL^1" for continuous u : R -> R, Federer 2.5.4(1), p. 95.
    Direct formalisation with the sealed measure L^1. *)
Theorem first_coordinate_integral_lebesgue (u : R -> R) :
  continuous u ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[0, 1]
    (real_total_integrand u) (plane_section_integral (fun x : (R * R)%type => u x.1))%:E.
Proof. by move=> hu; exact: (lebesgue_riemann_continuous_segment hu ltr01). Qed.

End PlaneSectionLebesgue.
