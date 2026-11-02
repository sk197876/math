(** Federer (1969), 2.4.12, pp. 87–88: the vector integral is continuous
    with norm at most one. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureLpConvergence MeasureVectorIntegralUP MeasureVectorIntegralAddition
  MeasureVectorIntegralScale MeasureVectorIntegralAlmostEquality MeasureVectorIntegralBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_vector_integral_subtract]: supporting
    subtractive linearity in Federer 2.4.12, pp. 87–88,
    on exact common partial domains. *)
Lemma measure_vector_integral_subtract (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (real_norm_metric_space hN)) (y z : V) :
  is_measure_vector_integral mu f y -> is_measure_vector_integral mu g z ->
  is_measure_vector_integral mu (partial_vector_subtract f g) (y-z)%R.
Proof.
move=> hf hg.
have hneg := @measure_vector_integral_scale R X V N hN mu hm (-1)%R g z hg.
rewrite scaleN1r in hneg.
have hi := @measure_vector_integral_add R X V N hN mu hm f _ y (-z)%R hf hneg.
apply: (@measure_vector_integral_almost_equal R X V N hN mu hm _ _ _ hi).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
  (@measure_almost_everywhere_and R X mu hm _ _
    (measurable_function_domain hf.1.2.1.1) (measurable_function_domain hg.1.2.1.1))).
move=> x [[u hu] [v hv]]; exists (u-v)%R; split.
- apply/partial_vector_add_graph; exists u,(-v)%R; split=> //; split=> //.
  apply/partial_vector_scale_graph; exists v; split=> //; by rewrite scaleN1r.
- apply/partial_vector_subtract_graph; exists u,v; by split=> //; split.
Qed.

(** Source for [measure_vector_integral_distance_bound]: direct Lipschitz
    estimate implicit in the continuous linear map of Federer 2.4.12, pp.
    87–88 Integral witnesses are compared without exposing or presupposing
    their construction. *)
Theorem measure_vector_integral_distance_bound (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (real_norm_metric_space hN)) (y z : V) :
  is_measure_vector_integral mu f y -> is_measure_vector_integral mu g z ->
  (N (y-z)%R)%:E <= measure_lp_distance mu N 1%R f g.
Proof.
move=> hf hg; exact (@measure_vector_integral_norm_bound R X V N hN mu hm _ _
  (@measure_vector_integral_subtract R X V N hN mu hm f g y z hf hg)).
Qed.
