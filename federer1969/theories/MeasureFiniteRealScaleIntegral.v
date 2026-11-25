(** Federer (1969), 2.4.12, pp. 87–88: integration of elementary
    vector-valued functions by scalar evaluation. This supporting scalar
    lemma combines 2.4.4(3), p. 82, with the zero case on finite-valued
    functions. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostBasic MeasurableFunctionUP MeasureIntegralUP MeasureStepIntegralIdentification
  MeasureUpperIntegralScale MeasureIntegralScaleLaw MeasureIntegralGraphEquivalence
  MeasureFiniteCharacteristicIntegral MeasureConullZeroIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_finite_real_total_scale_integral]: supporting scalar
    multiplication used for the elementary integrals in Federer 2.4.12, pp.
    87–88 The scalar and integral are finite, and scalar zero is included. *)
Lemma measure_finite_real_total_scale_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (u : X -> real_line_metric R) (b c : R) :
  is_measure_integral mu (partial_real_function_embed (partial_function_total u)) b%:E ->
  is_measure_integral mu (partial_real_function_embed
    (partial_function_total (fun x => ((c*u x)%R : real_line_metric R)))) (c*b)%:E.
Proof.
move=> hi; have [->|hc] := eqVneq c 0%R.
- rewrite mul0r; apply: (@measure_almost_zero_integral R X mu hm).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
  move=> x _; exists 0%R; split=> //; change ((0*u x)%R=0%R); by rewrite mul0r.
- rewrite EFinM.
  have hs := @measure_integral_nonzero_scale R X mu hm c _ b%:E hc hi.
  exact: measure_integral_graph_equivalent (real_total_scale_embedding_graph c u) hs.
Qed.
