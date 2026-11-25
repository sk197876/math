(** Federer (1969), 2.4.19, p. 91: the finite-image case of Jensen's
    inequality. This supporting formula retains partial domains and
    arbitrary dimension. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureStepFunctionUP
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureLpMembershipUP
  MeasureVectorIntegralUP MeasureVectorIntegralAlmostEquality MeasureVectorFiniteSumIntegral
  MeasureVectorFibreIntegral FiniteDeltaVectorSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_vector_integral_fibre_formula]: supporting
    finite-image computation in Federer 2.4.19, p. 91 The formula is proved
    from the abstract dual specification using characteristic integrals; no
    private vector-integral construction is imported or unfolded. *)
Theorem finite_vector_integral_fibre_formula (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) :
  is_measure_lp_function mu 1%R f -> finite_set (partial_function_range f) ->
  is_measure_vector_integral mu f
    (\sum_(y <- fset_set (partial_function_range f))
      fine (mu (partial_function_preimage f [set y])) *: y)%R.
Proof.
move=> hf hfinite.
pose F := fset_set (partial_function_range f).
pose s (y : V) := @CharacteristicFunction.value R X (partial_function_preimage f [set y]).
have hs y := @CharacteristicFunction.laws R X (partial_function_preimage f [set y]).
pose u (y : V) x := (s y x *: y : real_norm_metric_space hN).
pose z (y : V) := (fine (mu (partial_function_preimage f [set y])) *: y)%R.
have hi y : y \in (F : seq V) -> is_measure_vector_integral mu (partial_function_total (u y)) (z y).
  move=> _; exact (@measure_vector_fibre_integral R X V N hN mu hm f y
    (s y : X -> real_line_metric R) hf (hs y)).
have hsum := @measure_vector_total_finite_sum_integral R X V V N hN mu hm (F : seq V) u z hi.

apply: (@measure_vector_integral_almost_equal R X V N hN mu hm _ _ _ hsum).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ (measurable_function_domain hf.2.1.1)).
move=> x [v hv]; exists v; split=> //.
have hvF : v \in (F : seq V).
  rewrite /F in_fset_set //; apply/mem_set; by exists x.
have hcv : s v x = 1%R.
  apply: (characteristic_on_set (hs v)); exists v; by split.
have hc0 y : y != v -> s y x=0%R.
  move=> hy; apply: (characteristic_off_set (hs y))=> [[w [hw he]]].
  have evw := partial_function_single_valued hv hw.
  apply: (negP hy); apply/eqP; by rewrite -evw in he; symmetry.
exact (@finite_delta_vector_sum R V (F : seq V) v (fun y => s y x) (fset_uniq F) hvF hcv hc0).
Qed.
