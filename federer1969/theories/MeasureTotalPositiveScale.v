(** Federer (1969), 2.4.4(3), p. 82: positive scalar homogeneity, in the
    total extended-valued form used for the repeated-integral series of
    2.6.2(4), p. 117. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureIntegralUP MeasureIntegralScaleLaw MeasureIntegralGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ereal_scope.

(** Source for [measure_total_positive_scale_integral]: supporting
    total-function adapter for the positive scalar law of
    Federer 2.4.4(3), p. 82, applied in 2.6.2(4), p. 117. *)
Lemma measure_total_positive_scale_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> extended_real_line R) (c : R) a :
  (0 < c)%R -> is_measure_integral mu (partial_function_total f) a ->
  is_measure_integral mu (partial_function_total (fun x => c%:E*f x)) (c%:E*a).
Proof.
move=> hc hi; have h := @measure_integral_positive_scale R X mu hm c (partial_function_total f) a hc hi.
apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ h)=> x y; split.
- move=> [z [hz hy]]; change (c%:E*f x = y); by rewrite (hz : f x = z).
- move=> hy; exists (f x); by split.
Qed.
