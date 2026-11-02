(** Federer (1969), 2.4.12, pp. 87–88: the elementary pieces of a
    finite-image L1 function have vector integrals. Nonzero fibres have
    finite measure; the zero fibre contributes the zero vector even if its
    measure is infinite. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureBasic CharacteristicFunctionUP MeasureLpMembershipUP MeasureLpFiniteFibres
  MeasureVectorIntegralUP MeasureVectorIntegralZero MeasureVectorCharacteristicIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_vector_fibre_integral]: supporting elementary
    summands in the finite-image argument of Federer 2.4.12, pp. 87–88 No
    finiteness is imposed on the zero fibre. *)
Lemma measure_vector_fibre_integral (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) (y : V)
    (s : X -> real_line_metric R) :
  is_measure_lp_function mu 1%R f ->
  is_characteristic_function (partial_function_preimage f [set y]) s ->
  is_measure_vector_integral mu
    (partial_function_total (fun x => (s x *: y : real_norm_metric_space hN)))
    (fine (mu (partial_function_preimage f [set y])) *: y)%R.
Proof.
move=> hf hs; have [->|hy] := eqVneq y 0%R.
- rewrite scaler0.
  have he : (fun x => (s x *: 0%R : real_norm_metric_space hN)) = (fun _ : X => 0%R).
    by apply: funext=> x; rewrite scaler0.
  rewrite he; exact (@measure_vector_integral_zero R X V N hN mu hm).
- have [hA hfinite] := @measure_lp_nonzero_fibre_finite R X V N hN mu hm 1%R f y hf hy.
  have hfin : mu (partial_function_preimage f [set y]) \is a fin_num.
    by rewrite (ge0_fin_numE (measure_nonnegative hm _)).
  have hb : mu (partial_function_preimage f [set y]) = (fine (mu (partial_function_preimage f [set y])))%:E.
    by rewrite fineK.
  exact (@measure_vector_characteristic_integral R X V N hN mu hm _ s _ y hs hA hb).
Qed.
