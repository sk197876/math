(** Federer (1969), 3.2.20, p. 257: measurable finite
    ceilings for truncating an extended-real weighted integrand,
    using numerical closure in 2.3.2, p. 74. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealPartial PartialFunctionUP PartialFunctionBasic
  PartialFunctionPostcomposition MeasureUP MeasurableFunctionUP MeasurableGraphEquivalence
  MeasurableExtendedScale MeasurableExtendedMinimum FiniteWeightTruncationAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_finite_density_ceiling]: supporting finite
    ceiling times density in the increasing-convergence argument for
    Federer 3.2.20, p. 257. The density may vanish. *)
Lemma measurable_finite_density_ceiling (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : X -> R) (c : R) :
  c!=0%R ->
  is_measure_measurable_function mu (partial_function_total (fun x=>(p x)%:E : extended_real_line R)) ->
  is_measure_measurable_function mu (partial_function_total (fun x=>(c* p x)%R%:E : extended_real_line R)).
Proof.
move=> hc hp.
have hs := @measurable_extended_nonzero_scale R X mu hm c
  (partial_function_total (fun x=>(p x)%:E : extended_real_line R)) hc hp.
apply: (@measurable_function_graph_equivalent R X (extended_real_line R) mu _ _ _ hs)=> x y.
split.
- move=> [z [<- hz]]; by rewrite -EFinM in hz.
- move=> hy; exists (p x)%:E; split; first reflexivity; by rewrite -EFinM.
Qed.

(** Source for [measurable_finite_weighted_truncation]: supporting
    measurable truncation in Federer 3.2.20, p. 257.
    Only the weighted positive part and the finite density are assumed
    measurable; the original unweighted function need not be measurable. *)
Lemma measurable_finite_weighted_truncation (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (g : X -> \bar R) (p h : X -> R) (c : R) :
  c!=0%R -> (forall x,(0<=p x)%R) ->
  (forall x,(h x)%:E=Order.min (extended_positive_part (g x)) c%:E) ->
  is_measure_measurable_function mu (partial_function_total (fun x=>(p x)%:E : extended_real_line R)) ->
  is_measure_measurable_function mu
    (partial_function_total (fun x=>extended_positive_part (g x* (p x)%:E) : extended_real_line R)) ->
  is_measure_measurable_function mu
    (partial_function_total (fun x=>(h x)%:E* (p x)%:E : extended_real_line R)).
Proof.
move=> hc hp hClip hpMeas hu.
have hCeil := measurable_finite_density_ceiling hm hc hpMeas.
have hMin := measurable_total_extended_minimum hm hu hCeil.
apply: (@measurable_function_graph_equivalent R X (extended_real_line R) mu _ _ _ hMin)=> x y.
have he := finite_weighted_truncation_product (hp x) (hClip x).
by change (Order.min (extended_positive_part (g x* (p x)%:E)) (c* p x)%R%:E=y <->
  (h x)%:E* (p x)%:E=y); rewrite he.
Qed.
