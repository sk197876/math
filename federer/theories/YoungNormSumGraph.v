(** Federer (1969), 2.4.14, p. 88: the weighted sum of the normalised powers
    in the Holder proof. These supporting graph and integral identities
    isolate the arithmetic mean used in the equality argument. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealPartial PartialFunctionUP PartialNormPower
  RealPower PartialExtendedArithmetic MeasureUpperIntegralScale DominatedErrorGraphs
  MeasureYoungNormProduct MeasureUP MeasureIntegralUP MeasureIntegralScaleLaw MeasureIntegralAddition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_young_norm_sum_graph]: supporting
    evaluation of the arithmetic mean in Federer 2.4.14,
    p. 88. The displayed values exist on the common
    partial domain, with no exceptional default values. *)
Lemma partial_young_norm_sum_graph (R : realType) (X Y Z : Type)
    (N : Y -> R) (M : Z -> R) (p q : R)
    (f : partial_function X Y) (g : partial_function X Z) x a b :
  partial_function_graph f x a -> partial_function_graph g x b ->
  partial_function_graph (partial_young_norm_sum N M p q f g) x
    (p^-1*real_power (N a) p + q^-1*real_power (M b) q)%:E.
Proof.
move=> ha hb; apply: partial_finite_sum_graph.
- exists (real_power (N a) p)%:E; split; first by exists a; split.
  by rewrite EFinM.
- exists (real_power (M b) q)%:E; split; first by exists b; split.
  by rewrite EFinM.
Qed.

(** Source for [measure_young_norm_sum_unit_integral]: the integral of the
    normalised weighted sum equals one in Federer 2.4.14, proof p. 88 The
    two powered integrals are assumed to have their normalised unit values. *)
Lemma measure_young_norm_sum_unit_integral (R : realType) (X : choiceType) (Y Z : Type)
    (N : Y -> R) (M : Z -> R) (p q : R)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X Y) (g : partial_function X Z) :
  (0 < p)%R -> (0 < q)%R -> (p^-1 + q^-1 = 1)%R ->
  is_measure_integral mu (partial_norm_power N p f) 1 ->
  is_measure_integral mu (partial_norm_power M q g) 1 ->
  is_measure_integral mu (partial_young_norm_sum N M p q f g) 1.
Proof.
move=> hp hq hpq hf hg.
have hpi : (0 < p^-1)%R by rewrite invr_gt0.
have hqi : (0 < q^-1)%R by rewrite invr_gt0.
have hl := @measure_integral_positive_scale R X mu hm p^-1 _ 1 hpi hf.
have hr := @measure_integral_positive_scale R X mu hm q^-1 _ 1 hqi hg.
rewrite mule1 in hl.
rewrite mule1 in hr.
have hadd : extended_add (p^-1)%:E (q^-1)%:E = Some (1 : \bar R).
  by rewrite /extended_add /= -EFinD hpq.
have hs := @measure_integral_add R X mu hm _ _ _ _ _ hl hr hadd.
exact hs.
Qed.
