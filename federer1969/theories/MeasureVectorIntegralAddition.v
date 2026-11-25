(** Federer (1969), 2.4.12, pp. 87–88: linearity of the vector integral
    defined by dual evaluations. This law concerns any supplied integral
    witnesses; existence and selection remain separate. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic
  ExtendedRealPartial MeasureUP MeasureLpSumMembership MeasureIntegralAddition MeasureIntegralGraphEquivalence
  MeasureVectorIntegralUP PartialFunctionalArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_vector_integral_add]: direct additivity of the
    vector integral in Federer 2.4.12, pp. 87–88 Partial-domain sums use the
    common domain; the result satisfies the full integral specification. *)
Theorem measure_vector_integral_add (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (real_norm_metric_space hN)) (y z : V) :
  is_measure_vector_integral mu f y -> is_measure_vector_integral mu g z ->
  is_measure_vector_integral mu (partial_vector_add f g) (y+z)%R.
Proof.
move=> [hf hi] [hg hj]; split.
- exact (@measure_lp_function_add R X V N hN mu hm 1%R f g hf hg).
- move=> a ha; rewrite linearD EFinD.
  have hd : extended_add (a y)%:E (a z)%:E = Some ((a y)%:E+(a z)%:E) by [].
  have hsum := @measure_integral_add R X mu hm _ _ _ _ _ (hi a ha) (hj a ha) hd.
  exact: measure_integral_graph_equivalent (partial_functional_add_graph f g a) hsum.
Qed.
