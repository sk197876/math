(** Federer (1969), 2.9.23, p. 169: a proposed L1 weak limit is contradicted
    by characteristic tests on shrinking intervals. This supporting step
    uses the small-set absolute integral estimate of 2.4.11, pp. 85–86,
    rather than constructing an oscillating L-infinity test. Chapter 21
    omits 2.9.23. The local Federer erratum has no entry for this example. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP
  PartialFunctionBasic PartialAbsolutePartsGraph PartialZeroExtension MeasureUP
  MeasureIntegralUP MeasureIntegralAbsolute MeasureIntegralAbsoluteContinuity
  MeasureIntegralGraphEquivalence MeasureIntegralUniqueness MeasureSubsetIntegral
  CharacteristicFunctionUP CharacteristicFunctionSealed SummableRealFunctionUP
  SummableRealSpace SummableCharacteristicFunctional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [characteristic_absolute_zero_extension_graph]: supporting
    identity |f chi_A|=(|f|)_A for the small-test argument in
    Federer 2.9.23, p. 169, using the subset convention
    of 2.4.10, p. 85. It is pointwise, including null sets. *)
Lemma characteristic_absolute_zero_extension_graph (R : realType) (X : Type)
    (A : set X) (s f : X -> R) : is_characteristic_function A s ->
  forall x z, partial_function_graph
      (partial_function_zero_extension (0 : extended_real_line R) A
        (partial_extended_function_absolute_value (real_total_integrand f))) x z <->
    partial_function_graph (partial_extended_function_absolute_value
      (real_total_integrand (fun t => f t*s t))) x z.
Proof.
move=> hs x z; case: (pselect (A x))=> hx.
- rewrite (partial_function_zero_extension_on _ _ _ hx).
  split=> [[y [hy he]]|[y [hy he]]]; exists y; split=> //;
    move: hy; rewrite !real_total_integrand_graph (characteristic_on_set hs hx) mulr1;
    by [].
- rewrite (partial_function_zero_extension_off _ _ _ hx).
  split.
  + move=> ->; exists 0%:E; split; last exact: abse0.
    apply/real_total_integrand_graph; by rewrite (characteristic_off_set hs hx) mulr0.
  + move=> [y [hy he]].
    have hy0 : (0 : \bar R)=y.
      by move: hy; rewrite real_total_integrand_graph (characteristic_off_set hs hx) mulr0.
    by rewrite -hy0 abse0 in he; symmetry.
Qed.

(** Source for [summable_characteristic_absolute_bound]: supporting
    inequality |integral_A f|<=integral_A |f| in Federer 2.9.23,
    p. 169, by 2.4.4(7), p. 82. Both asserted values
    are actual integrals; no bound on mu(A) is needed here. *)
Lemma summable_characteristic_absolute_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (hA : measure_measurable mu A) (f : summable_real_space hm) (a : R) :
  is_measure_subset_integral mu A
    (partial_extended_function_absolute_value (real_total_integrand (summable_real_value f))) a%:E ->
  `|summable_characteristic_functional hA f|<=a.
Proof.
move=> hi.
have hj := (summable_characteristic_functional_specification hA f).1.
have [b [hb hbound]] := @measure_integral_absolute_bound R X mu hm _ _ hj.
have ha := @measure_integral_graph_equivalent R X mu _ _ _
  (@characteristic_absolute_zero_extension_graph R X A _ (summable_real_value f)
    (@CharacteristicFunction.laws R X A)) hi.
have he := measure_integral_unique hb ha.
by rewrite he abse_EFin lee_fin in hbound.
Qed.

(** Source for [summable_characteristic_small_sets]: supporting uniform
    smallness of characteristic tests for an L1 candidate weak limit in
    Federer 2.9.23, p. 169. The proof applies the full 2.4.11 estimate, pp.
    85–86, for every measurable set of sufficiently small measure. *)
Lemma summable_characteristic_small_sets (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : summable_real_space hm) (e : R) : 0<e ->
  exists d : R, 0<d /\ forall (A : set X) (hA : measure_measurable mu A),
    (mu A<=d%:E)%E -> `|summable_characteristic_functional hA f|<e.
Proof.
move=> he.
have [d [hd hsmall]] := @measure_integral_absolute_continuity R X mu hm
  (real_total_integrand (summable_real_value f)) e (summable_real_value_summable f) he.
exists d; split=> // A hA hAd.
have [a [ha hae]] := hsmall A hA hAd.
exact: le_lt_trans (summable_characteristic_absolute_bound hA ha) hae.
Qed.
