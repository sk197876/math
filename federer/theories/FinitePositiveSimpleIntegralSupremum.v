(** Federer (1969), 2.5.3, proof p. 95: passage from characteristic
    functions to positive finite linear combinations, then to a nonnegative
    summable function. The finite test sums in 2.4.6, p. 84, give an
    equivalent supremum argument. We derive the reduction directly from the
    lower-integral specification and finite subsums of step functions,
    retaining partial domains. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology ExtendedRealPartial PartialFunctionUP
  MeasureUP MeasureBasic MeasureFiniteClosure MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  PartialExtendedOrderLoci MeasureStepFunctionUP MeasureStepFibres MeasureIntegralUP
  NonnegativeSum NumericalSum NumericalSumOrder FatouNullRestriction MeasureFiniteSimpleComparison ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_positive_finite_simple_minorant]: supporting finite
    disjoint tests in Federer 2.4.6, p. 84, used for the finite-combination
    step in 2.5.3, p. 95 Coefficients index their sets, and are strictly
    positive on the finite index set. *)
Definition is_positive_finite_simple_minorant (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f : partial_function X (extended_real_line R))
    (C : {fset R}) (A : R -> set X) :=
  (forall y, y \in C -> measure_measurable mu (A y)) /\
  (forall y z, y \in C -> z \in C -> y != z -> forall x, A y x -> A z x -> False) /\
  (forall y, y \in C -> (0 < y)%R) /\
  (forall y, y \in C -> forall x, A y x -> exists z, partial_function_graph f x z /\ y%:E <= z).

(** Source for [positive_finite_simple_integral_values]: supporting
    finite-sum values for the reduction in Federer 2.5.3, p. 95, using the
    test sums of 2.4.6, p. 84 *)
Definition positive_finite_simple_integral_values (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f : partial_function X (extended_real_line R)) :=
  [set a | exists C A, is_positive_finite_simple_minorant mu f C A /\ a=\sum_(y <- C) y%:E*mu (A y)].

(** Source for [positive_finite_simple_integral_supremum]: supporting
    positive simple approximation for Federer 2.5.3, p. 95 The
    lower-integral and finite-subsum laws replace a chosen approximation
    sequence; no finiteness of the ambient measure is imposed. *)
Theorem positive_finite_simple_integral_supremum (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) a :
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f) ->
  is_measure_integral mu f a ->
  is_extended_real_supremum (positive_finite_simple_integral_values mu f) a.
Proof.
move=> hp hi; constructor.
- move=> b [C [A [[hA [hd [hc hf]]] ->]]].
  exact: (@measure_finite_simple_lower_bound R X R mu hm C A (fun y => y) f a hA hd hc hf hp hi).
- move=> d hd; apply: hi.2.2.2=> b [u [[hu huf] hb]].
  pose E := partial_step_lower_locus u f.
  have hE : measure_almost_everywhere mu E := huf.
  have hEm := @measure_conull_set_measurable R X mu hm E hE.
  pose A y := partial_function_preimage u [set y] `&` E.
  have hA y : measure_measurable mu (A y).
    exact: (@measure_measurable_intersection R X mu hm _ _
      (@measurable_real_fibre R X mu hm u (step_function_measurable hu) y) hEm).
  have hAe y : mu (A y)=mu (partial_function_preimage u [set y]).
    exact: (@measure_conull_intersection_value R X mu hm E _ hE).
  pose c (y : R) := y%:E*mu (partial_function_preimage u [set y]).
  pose p (y : R) := extended_positive_part (c y).
  have hp0 y : (@setT R) y -> 0 <= p y by move=> _; exact: extended_positive_part_nonnegative.
  have hbp : b <= nonnegative_sum setT p.
    apply: (@numerical_sum_values_mono R R setT c p b (nonnegative_sum setT p))=> //.
    + by move=> y _; rewrite /p /extended_positive_part le_max lexx.
    + exact: numerical_sum_nonnegative hp0.
  apply: le_trans hbp _; apply: nonnegative_sum_least=> C _.
  pose D := [fset y in C | (0 < y)%R].
  have hsum : (\sum_(y <- C) p y)=\sum_(y <- D) y%:E*mu (A y).
    rewrite /D -big_fset_condE [in RHS]big_mkcond.
    apply: eq_big_seq=> y hy; have [hy0|hy0] := ltP 0%R y.
    + rewrite hAe /p /c /extended_positive_part max_l //.
      apply: mule_ge0; first by rewrite lee_fin ltW.
      exact: measure_nonnegative.
    + rewrite /p /c /extended_positive_part max_r //.
      apply: mule_le0_ge0; first by rewrite lee_fin.
      exact: measure_nonnegative.
  rewrite hsum; apply: hd; exists D,A; split; last by [].
  split; first by move=> y _; exact: hA.
  split.
  + move=> y z hy hz hne x [[v [hv ev]] _] [[w [hw ew]] _].
    have he := partial_function_single_valued hv hw.
    apply: (negP hne); apply/eqP; by rewrite -ev -ew.
  + split; first by move=> y; rewrite /D inE=> /andP[_ hy].
    move=> y hy x [[v [hv ev]] [w [z [hw [hz hwz]]]]].
    have he := partial_function_single_valued hv hw.
    exists z; split=> //; by rewrite -ev he.
Qed.
