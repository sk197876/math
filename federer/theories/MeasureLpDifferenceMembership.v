(** Federer (1969), 2.4.12, pp. 86–88: differences in the Lp spaces, used to
    prove continuity of scalar and vector integration. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureLpMembershipUP MeasureLpSumMembership MeasureLpScaleMembership MeasureLpAlmostEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lp_function_subtract]: supporting full Lp
    membership of a difference in Federer 2.4.12, pp. 86–88.
    Pointwise subtraction uses the exact common partial domain. *)
Lemma measure_lp_function_subtract (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f g : partial_function X (real_norm_metric_space hN)) :
  is_measure_lp_function mu p f -> is_measure_lp_function mu p g ->
  is_measure_lp_function mu p (partial_vector_subtract f g).
Proof.
move=> hf hg.
have hneg := @measure_lp_function_scale R X V N hN mu hm p (-1)%R g hg.
have hs := @measure_lp_function_add R X V N hN mu hm p f _ hf hneg.
apply: (@measure_lp_function_almost_equal R X V N hN mu hm p _ _ hs).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
  (@measure_almost_everywhere_and R X mu hm _ _
    (measurable_function_domain hf.2.1.1) (measurable_function_domain hg.2.1.1))).
move=> x [[u hu] [v hv]]; exists (u-v)%R; split.
- apply/partial_vector_add_graph; exists u,(-v)%R; split=> //; split=> //.
  apply/partial_vector_scale_graph; exists v; split=> //; by rewrite scaleN1r.
- apply/partial_vector_subtract_graph; exists u,v; by split=> //; split.
Qed.
