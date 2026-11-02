(** Federer (1969), 2.9.22, pp. 167–168: normed versions of conditions (1),
    (2) and (4) of 2.9.20, p. 165. Vector integrals and scalar subset
    integrals are actual relations for the exact partial derivative. The
    closed-segment continuity and open-interval restrictions follow the
    printed conventions. No relevant erratum entry. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground CurveVariationUP
  NormedCurveDerivativeUP NormedCurveDerivativeIntegrands MeasureVectorIntegralUP
  MeasureSubsetIntegral MeasureRestriction MeasureAbsoluteContinuity LebesgueScalarMeasure StieltjesImageMeasures.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normed_curve_indefinite_derivative_integral]: direct
    extension of 2.9.20(1), p. 165, in Federer 2.9.22,
    pp. 167–168. The actual vector integral of the exact partial
    derivative over [a,x] is the increment g(x)-g(a), at every
    x in [a,b]. The integral includes its full L1 requirements. *)
Definition normed_curve_indefinite_derivative_integral (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> real_norm_metric_space hN) (a b : R) :=
  forall x : R, a<=x -> x<=b -> @is_measure_vector_integral R (real_line_metric R) E N hN
    (measure_restrict (@lebesgue_scalar_measure R) (`[a,x] : set (real_line_metric R)))
    (normed_curve_derivative hN g) (g x-g a).
Arguments normed_curve_indefinite_derivative_integral {R E N} hN g a b.

(** Source for [normed_curve_variation_integral_equality]: direct
    extension of 2.9.20(2), p. 165, in Federer 2.9.22,
    pp. 167–168. Use the actual partial N(g') subset integral
    and the original partition-supremum variation, including existence
    of the integral; no independently chosen variation object appears. *)
Definition normed_curve_variation_integral_equality (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> real_norm_metric_space hN) (a b : R) :=
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
    (normed_curve_norm_derivative_integrand hN g) (curve_variation g a b).
Arguments normed_curve_variation_integral_equality {R E N} hN g a b.

(** Source for [normed_curve_continuous_induced_measures]: direct
    extension of 2.9.20(4), p. 165, in Federer 2.9.22,
    p. 167. Require relative norm continuity on the closed segment
    and absolute continuity of the two open-interval restricted
    measures for every continuous dual scalarisation. The supplied
    pairing identifies the dual; existence of each actual induced pair
    is proved separately from locally finite variation. *)
Definition normed_curve_continuous_induced_measures (R : realType) (E D : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (ed : Hom D (Hom E R^o))
    (g : R -> real_norm_metric_space hN) (a b : R) :=
  {within (`[a,b] : set (real_line_metric R)),
    continuous (g : real_line_metric R -> real_norm_metric_space hN)} /\
  forall alpha : D, forall psip psim : set R -> \bar R,
    is_induced_measure_pair (fun t => ed alpha (g t)) psip psim ->
    is_absolutely_continuous_measure (measure_restrict psip `]a,b[) (@lebesgue_scalar_measure R) /\
    is_absolutely_continuous_measure (measure_restrict psim `]a,b[) (@lebesgue_scalar_measure R).

Arguments normed_curve_continuous_induced_measures {R E D N} hN ed g a b.
