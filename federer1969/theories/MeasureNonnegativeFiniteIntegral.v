(** Federer (1969), proof of 2.4.4(2), p. 83: integrability of an
    almost-everywhere nonnegative measurable function whose values are
    finite almost everywhere. The integral itself may be infinite. Source
    editions: MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureUP MeasureAlmostUP MeasurableFunctionUP
  PartialExtendedOrderLoci MeasureIntegralUP MeasureIntegralBounds MeasureIntegralSqueeze
  MeasureNonnegativeLowerIntegral ExtendedGeometricSqueeze GeometricQuantisationUP GeometricQuantisationSealed
  MeasureGeometricSandwich.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_almost_finite_function_integral]:
    second case in Federer's proof of 2.4.4(2), p. 83.
    For every t>1, a sealed geometric lower approximant u
    has t*u as an upper approximant; the integral bounds coincide. *)
Theorem nonnegative_almost_finite_function_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  is_measure_measurable_function mu f ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f) ->
  measure_almost_everywhere mu (partial_extended_below_infinity_locus f) ->
  is_measure_integral mu f (measure_lower_integral mu f) /\ 0 <= measure_lower_integral mu f.
Proof.
move=> hf hp hfin; have hl := @measure_lower_integral_nonnegative R X mu hm f hp.
split=> //; apply: (@measure_integral_squeeze R X mu hm f _ hf); last exact: lexx.
apply: extended_geometric_squeeze hl _ => t ht.
exact (@measure_geometric_integral_bound R X mu hm t (@GeometricQuantisation.value R t ht) f
  ht (@GeometricQuantisation.laws R t ht) hf hp hfin).
Qed.
