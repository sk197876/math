(** Federer (1969), 2.4.12, pp. 86-87: almost-everywhere invariance
    supporting partial-domain Lp membership and finite-image density. These
    supporting consequences permit total representatives without changing
    the original partial-domain definitions. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableNormedFunctionUP
  MeasurableNormedBasic MeasurableNormedDifference MeasureLpNorm MeasureLpNormAlmostEquality
  MeasureLpMembershipUP MeasureLpCountableMeasurability MeasureLpConvergence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lp_function_almost_equal]: supporting
    invariance of finite-p Lp membership in Federer 2.4.12,
    p. 86, under the almost-equality convention of 2.3.1,
    p. 72. Countable measurability follows from the finite norm. *)
Lemma measure_lp_function_almost_equal (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f g : partial_function X (real_norm_metric_space hN)) :
  is_measure_lp_function mu p f -> measure_almost_equal mu f g -> is_measure_lp_function mu p g.
Proof.
move=> hf he.
have hg := @measurable_normed_almost_equal R X V N hN mu hm f g hf.2.1 he.
have hn := @measure_lp_norm_almost_equal R X V N hN mu hm p f g hf.1 hf.2.1.1 hg.1 he.
have hfin : measure_lp_norm mu N p g < +oo by rewrite -hn; exact hf.2.2.1.
split; first exact hf.1.
split=> //; split=> //.
exact (@finite_lp_norm_countably_measurable R X V N hN mu hm p g hf.1 hg.1 hfin).
Qed.

(** Source for [measure_lp_distance_almost_left]: supporting
    transfer of finite-image approximations from a total representative
    to Federer's original partial function in 2.4.12, p. 87.
    A common conull domain supplies identical difference values. *)
Lemma measure_lp_distance_almost_left (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f F g : partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R -> is_measurable_normed_function mu f -> is_measurable_normed_function mu F ->
  is_measurable_normed_function mu g -> measure_almost_equal mu f F ->
  measure_lp_distance mu N p f g = measure_lp_distance mu N p F g.
Proof.
move=> hp hf hF hg he.
apply: (@measure_lp_norm_almost_equal R X V N hN mu hm p _ _ hp
  (@measurable_normed_function_subtract R X V N hN mu hm f g hf hg).1
  (@measurable_normed_function_subtract R X V N hN mu hm F g hF hg).1).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
  (@measure_almost_everywhere_and R X mu hm _ _ he (measurable_function_domain hg.1))).
move=> x [[u [hu hU]] [v hv]]; exists (u-v)%R; split;
  apply/partial_vector_subtract_graph; exists u,v; by split=> //; split.
Qed.
