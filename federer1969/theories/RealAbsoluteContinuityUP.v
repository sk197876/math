(** Federer (1969), 2.9.20, pp. 165–166: absolute continuity on a finite
    closed interval. No relevant correction occurs in Federer's local LaTeX
    erratum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import OrderedIntervalFamilyUP RealMetricBackground
  CurveVariationUP RealCurveDerivativeIntegrands MeasureSubsetIntegral
  LebesgueScalarMeasure MeasureRestriction MeasureAbsoluteContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_absolutely_continuous_real_curve]: direct condition (3)
    and final definition in Federer 2.9.20, p. 165 Retain both printed
    non-strict sum bounds and strict individual cell lengths. This law does
    not presume a derivative, continuity, induced measures or a chosen
    construction of the curve. *)
Definition is_absolutely_continuous_real_curve (R : realType) (g : R -> R)
    (a b : R) := forall epsilon : R, 0<epsilon -> exists delta : R,
  0<delta /\ forall s : seq (R * R), is_ordered_real_interval_family a b s ->
    real_interval_family_length s<=delta ->
    real_interval_family_increment_sum g s<=epsilon.

(** Source for [real_curve_indefinite_derivative_integral]: direct condition
    (1) in Federer 2.9.20, p. 165 Express the identity by the actual
    integral relation of the partial derivative, including its existence,
    rather than assigning a value to an undefined integral. *)
Definition real_curve_indefinite_derivative_integral (R : realType)
    (g : R -> R) (a b : R) := forall x : R, a<=x -> x<=b ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,x]
    (real_curve_derivative_integrand g) (g x-g a)%:E.

(** Source for [real_curve_variation_integral_equality]: direct condition
    (2) in Federer 2.9.20, p. 165 Use the book's abstract total variation
    and the actual partial absolute derivative integrand. *)
Definition real_curve_variation_integral_equality (R : realType)
    (g : R -> R) (a b : R) :=
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
    (real_curve_absolute_derivative_integrand g)
    (curve_variation (g : R -> real_line_metric R) a b).

(** Source for [real_curve_continuous_induced_measures]: direct condition
    (4) in Federer 2.9.20, p. 165 Continuity is relative to the closed
    segment, including its one-sided endpoint behaviour. The restrictions of
    both induced measures are to the open interval. Continuity cannot be
    inferred from their absolute continuity alone: isolated point spikes
    would be invisible to them. *)
Definition real_curve_continuous_induced_measures (R : realType)
    (g : R -> R) (psip psim : set R -> \bar R) (a b : R) :=
  {within (`[a,b] : set (real_line_metric R)),
    continuous (g : real_line_metric R -> real_line_metric R)} /\
  is_absolutely_continuous_measure (measure_restrict psip `]a,b[)
    (@lebesgue_scalar_measure R) /\
  is_absolutely_continuous_measure (measure_restrict psim `]a,b[)
    (@lebesgue_scalar_measure R).
