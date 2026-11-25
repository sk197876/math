(** Federer (1969), 2.4.12, pp. 87–88: the vector integral depends only on
    the almost-everywhere class of f, by its dual specification and scalar
    integral invariance, 2.4.3(2), p. 81. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionPostcomposition
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureLpAlmostEquality MeasureIntegralAlmostEquality
  MeasureVectorIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_vector_integral_almost_equal]: supporting
    invariance of vector integrals in Federer 2.4.12, pp. 87–88.
    Partial domains may differ on a null set; no arbitrary extension
    of either function is imposed. *)
Lemma measure_vector_integral_almost_equal (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (real_norm_metric_space hN)) (y : V) :
  is_measure_vector_integral mu f y -> measure_almost_equal mu f g ->
  is_measure_vector_integral mu g y.
Proof.
move=> [hf hi] he; split.
- exact (@measure_lp_function_almost_equal R X V N hN mu hm 1%R f g hf he).
- move=> a ha; apply: (@measure_integral_almost_equal R X mu hm _ _ _ (hi a ha)).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he).
  move=> x [z [hzf hzg]]; exists (a z)%:E; split; exists z; by split.
Qed.
