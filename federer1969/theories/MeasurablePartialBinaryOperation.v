(** Federer (1969), 2.3.2, p. 74: measurability of numerical operations when
    their actual domains are conull. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionPair PartialFunctionPostcomposition
  PartialFunctionBinaryOperation MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasurablePostcomposition MeasurableAlmostModification BorelContinuousRegion TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [measurable_partial_binary_operation]: supporting general
    form of the partial arithmetic argument in Federer 2.3.2, p. 74. Pair
    measurability and conull operation domain are separate hypotheses;
    target inhabitation is supplied by c. *)
Theorem measurable_partial_binary_operation (R : realType) (X : choiceType)
    (Y Z W : topologicalType) (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X Y) (g : partial_function X Z) (D : set (Y * Z))
    (h : Y * Z -> W) (c : W) :
  is_measure_measurable_function mu (partial_function_pair f g) ->
  borel_set D -> (forall p, D p -> {for p, continuous h}) ->
  measure_almost_everywhere mu (partial_function_domain (partial_function_binary_on f g D h)) ->
  is_measure_measurable_function mu (partial_function_binary_on f g D h).
Proof.
move=> hpair hD hc hd.
pose k p := if pselect (D p) then h p else c.
have hk := @borel_continuous_region_extension _ W D h c hD hc.
have hkm := @measurable_function_borel_postcomposition R X _ W mu hm
  (partial_function_pair f g) k hpair hk.
apply: (@measurable_function_almost_equal R X W mu hm _ _ hkm).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hd).
move=> x [w [p [hp [hDp he]]]]; exists w; split; last by exists p.
exists p; split=> //; rewrite /k; case: (pselect (D p))=> // hn.
Qed.
