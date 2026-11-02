(** Supporting finite-source examples for the nonhomogeneity and
    nonconvexity assertions in Federer (1969), 2.3.8, pp. 78–79; counting
    measure is defined in 2.1.2, p. 54. Source context:
    MeasurableNormedFunctionUP.v. These are local concrete witnesses, not
    examples separately printed in the book. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic MeasureUP MeasureBasic
  MeasureAlmostBasic MeasurableFunctionUP MeasurableNormedFunctionUP MeasurableNormedCountableRange
  CountingMeasure NonnegativeSum NonnegativeSumSupport NonnegativeSumBoolean.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [counting_measurable_total_function]: supporting
    measurability for the finite-source counterexamples to norm
    properties in Federer 2.3.8, pp. 78–79. Every
    subset is measurable for counting measure. *)
Lemma counting_measurable_total_function (R : realType) (X : choiceType)
    (Y : topologicalType) (f : X -> Y) :
  is_measure_measurable_function (@counting_measure R X) (partial_function_total f).
Proof.
constructor.
- rewrite partial_function_total_domain; exact: measure_almost_everywhere_true (counting_measure_is_measure R X).
- move=> U ho; exact: counting_measure_measurable.
Qed.

(** Source for [finite_source_normed_counting_function]: supporting
    membership in A(mu,Y) for the finite-source examples in
    Federer 2.3.8, pp. 78–79. The finite image lies
    in a separable closed linear span. *)
Lemma finite_source_normed_counting_function (R : realType) (X : finType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (f : X -> real_norm_metric_space hN) :
  is_measurable_normed_function (@counting_measure R X) (partial_function_total f).
Proof.
apply: (@measurable_normed_countable_total_range R X V N hN _ (counting_measure_is_measure R X)).
- exact: counting_measurable_total_function.
- apply: sub_countable (card_image_le _ _) _; exact: countableP.
Qed.

(** Source for [counting_singleton_value]: one-point measure
    calculation for the examples supporting Federer 2.3.8,
    pp. 78–79, from counting in 2.1.2, p. 54. *)
Lemma counting_singleton_value (R : realType) (X : choiceType) (x : X) :
  @counting_measure R X [set x] = 1.
Proof. by rewrite counting_measure_sum nonnegative_sum_singleton // lee_fin ler01. Qed.

(** Source for [counting_unit_whole_value]: unit total mass for
    the nonhomogeneity example supporting Federer 2.3.8, p. 78. *)
Lemma counting_unit_whole_value (R : realType) : @counting_measure R unit setT = 1.
Proof.
have he : @setT unit = [set tt] by apply/seteqP; split; move=> [] hx.
rewrite he; exact: counting_singleton_value.
Qed.

(** Source for [counting_boolean_whole_value]: total mass two
    for the nonconvexity example supporting Federer 2.3.8,
    pp. 78–79. *)
Lemma counting_boolean_whole_value (R : realType) : @counting_measure R bool setT = 2%:E.
Proof.
rewrite counting_measure_sum nonnegative_sum_bool; last by move=> b; rewrite lee_fin ler01.
by rewrite -EFinD.
Qed.
