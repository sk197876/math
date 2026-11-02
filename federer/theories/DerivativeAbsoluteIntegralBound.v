(** Federer (1969), 2.9.20, p. 166, proof of (1)=>(2): bound the absolute
    derivative integral of each increment using 2.4.4(7), p. 82. This graph
    adapter preserves the derivative's actual partial domain. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP
  PartialFunctionPostcomposition PartialAbsolutePartsGraph PartialZeroExtension
  PartialZeroExtensionLaws RealCurveDerivativeIntegrands MeasureUP
  MeasureSubsetIntegral MeasureIntegralAbsolute MeasureIntegralGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [derivative_zero_extension_absolute_graph]: supporting
    absolute-value convention for the calculation in Federer 2.9.20, p. 166
    Taking the absolute value of the zero extension of g' gives exactly the
    zero extension of the actual partial |g'|. *)
Lemma derivative_zero_extension_absolute_graph (R : realType) (g : R -> R)
    (A : set R) x y :
  partial_function_graph (partial_extended_function_absolute_value
    (partial_function_zero_extension (0 : extended_real_line R) A
      (real_curve_derivative_integrand g))) x y <->
  partial_function_graph (partial_function_zero_extension (0 : extended_real_line R) A
    (real_curve_absolute_derivative_integrand g)) x y.
Proof.
rewrite /partial_extended_function_absolute_value
  (@partial_zero_extension_postcompose R (extended_real_line R) (extended_real_line R)
    0 0 A (real_curve_derivative_integrand g) (fun z => `|z|) x y abse0)
  !partial_function_zero_extension_graph.
split.
- move=> [[hA [z [[v [hv he]] hz]]]|hzero]; last by right.
  left; split=> //; exists v; split=> //.
  by rewrite -he abse_EFin in hz.
- move=> [[hA [v [hv he]]]|hzero]; last by right.
  left; split=> //; exists v%:E; split; first by exists v; split.
  by rewrite abse_EFin.
Qed.

(** Source for [derivative_subset_integral_absolute_bound]: supporting
    absolute integral estimate used in Federer 2.9.20, p. 166, first
    displayed inequality A finite signed derivative integral yields an
    actual absolute derivative integral dominating its absolute value. This
    helper permits any measurable space measure over R and any target set. *)
Lemma derivative_subset_integral_absolute_bound (R : realType) (g : R -> R)
    (mu : set R -> \bar R) (A : set R) (z : R) : is_measure mu ->
  is_measure_subset_integral mu A (real_curve_derivative_integrand g) z%:E ->
  exists I : \bar R, is_measure_subset_integral mu A
    (real_curve_absolute_derivative_integrand g) I /\ `|z|%:E<=I.
Proof.
move=> hm hI.
have [J [hJ hb]] := measure_integral_absolute_bound hm hI.
exists J; split; last by move: hb; rewrite abse_EFin.
exact: measure_integral_graph_equivalent (derivative_zero_extension_absolute_graph g A) hJ.
Qed.
