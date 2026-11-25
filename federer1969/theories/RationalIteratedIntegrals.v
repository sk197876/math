(** Federer (1969), 2.6.3(2), p. 118: both iterated integrals of the printed
    rational kernel equal zero. The inner-integral functions below use the
    existing abstract parameterized integral; their domains are proved to be
    the whole line. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialProductSections SummableRealFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureConullZeroIntegral
  MeasureExtendedCharacteristicIntegral PositiveCharacteristicMeasurability ParameterizedIntegral ParameterizedIntegralLaws
  LebesgueScalarMeasure RationalFubiniKernel RationalSectionIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rational_fubini_integrand]: the actual
    real-valued kernel of Federer 2.6.3(2), p. 117,
    in the project's existing partial-integral interface.
    Its domain is all of R times R, as in the book. *)
Definition rational_fubini_integrand (R : realType) :=
  real_total_integrand (fun p : R*R => rational_fubini_kernel p.1 p.2).

(** Source for [rational_section_integral_zero]: every horizontal section
    has integral zero in Federer 2.6.3(2), p. 118 Nonpositive parameters
    give the identically zero function; positive parameters use the proved
    improper integral. *)
Theorem rational_section_integral_zero (R : realType) (y : R) :
  is_measure_integral (@lebesgue_scalar_measure R)
    (real_total_integrand (fun x => rational_fubini_kernel x y)) 0%E.
Proof.
case: (lerP y 0)=> hy; last exact: rational_positive_section_integral hy.
apply: (measure_almost_zero_integral (lebesgue_scalar_is_measure R)).
apply: (@measure_almost_everywhere_mono R R _ (lebesgue_scalar_is_measure R)
  setT _ _ (measure_almost_everywhere_true (lebesgue_scalar_is_measure R)))=> x _.
apply/real_total_integrand_graph; by rewrite rational_fubini_kernel_nonpositive_right.
Qed.

(** Source for [rational_horizontal_integral_zero]: supporting
    identification of the exact horizontal partial section in
    the first iterated integral of Federer 2.6.3(2), p. 118. *)
Lemma rational_horizontal_integral_zero (R : realType) (y : R) :
  is_measure_integral (@lebesgue_scalar_measure R)
    (partial_product_horizontal_section (@rational_fubini_integrand R) y) 0%E.
Proof.
apply: (@measure_integral_graph_equivalent R R _ _ _ 0%E _ (@rational_section_integral_zero R y)).
by move=> x z.
Qed.

(** Source for [rational_vertical_integral_zero]: symmetry giving the other
    inner integral in Federer 2.6.3(2), p. 118 *)
Lemma rational_vertical_integral_zero (R : realType) (x : R) :
  is_measure_integral (@lebesgue_scalar_measure R)
    (partial_product_vertical_section (@rational_fubini_integrand R) x) 0%E.
Proof.
have he : (fun y => rational_fubini_kernel y x) = (fun y => rational_fubini_kernel x y).
  apply: funext=> y; exact: rational_fubini_kernel_symmetric.
have hi := @rational_section_integral_zero R x; rewrite he in hi.
apply: (@measure_integral_graph_equivalent R R _ _ _ 0%E _ hi).
by move=> y z.
Qed.

(** Source for [rational_fubini_iterated_integrals_zero]: both actual
    iterated integrals displayed in Federer 2.6.3(2), p. 118 Each inner
    integral is defined everywhere, and both outer integrals exist with the
    finite value zero. *)
Theorem rational_fubini_iterated_integrals_zero (R : realType) :
  is_measure_integral (@lebesgue_scalar_measure R)
    (parameterized_integral (@lebesgue_scalar_measure R)
      (partial_product_horizontal_section (@rational_fubini_integrand R))) 0%E /\
  is_measure_integral (@lebesgue_scalar_measure R)
    (parameterized_integral (@lebesgue_scalar_measure R)
      (partial_product_vertical_section (@rational_fubini_integrand R))) 0%E.
Proof.
have hm := lebesgue_scalar_is_measure R.
have hz := @nonnegative_extended_constant_integral R R _ hm 0%E (lexx (0%E : \bar R)).
rewrite mul0e in hz.
split; apply: (@parameterized_integral_total_outer_transfer R R R _ _ hm _ (fun _ => 0%E)).
- apply: (@measure_almost_everywhere_mono R R _ hm setT _ _ (measure_almost_everywhere_true hm))=> y _.
  exact: rational_horizontal_integral_zero.
- exact: hz.
- apply: (@measure_almost_everywhere_mono R R _ hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exact: rational_vertical_integral_zero.
- exact: hz.
Qed.
