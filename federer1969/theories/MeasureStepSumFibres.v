(** Federer (1969), 2.4.1, p. 81: group the common refinement by r+s=t to
    recover the fibre measure of u+v. Source context:
    MeasureStepFunctionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialFunctionPair PartialFunctionPostcomposition
  MeasureUP MeasureBasic MeasureFiniteClosure MeasureCountableAdditivity MeasurableFunctionUP
  MeasurableRealArithmetic MeasureStepFunctionUP MeasureStepFibres MeasureStepCommonRefinement
  NonnegativeSum NonnegativeSumSupport NonnegativeSumRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_real_sum_fibre_union]: supporting
    set equality for the final grouping in Federer 2.4.1,
    p. 81, retaining the exact common domain of the sum. *)
Lemma partial_real_sum_fibre_union (R : realType) (X : Type)
    (u v : partial_function X (real_line_metric R)) (t : R) :
  partial_function_preimage (partial_real_function_add u v) [set t] =
    \bigcup_(p in [set p : R * R | partial_function_range u p.1 /\
      partial_function_range v p.2 /\ (p.1+p.2)%R=t])
      (partial_function_preimage u [set p.1] `&` partial_function_preimage v [set p.2]).
Proof.
apply/seteqP; split=> x.
- move=> [z [[[r s] [[hr hs] he]] ht]].
  exists (r,s).
  + split; first by exists x.
    split; first by exists x.
    by rewrite he ht.
  + split; [exists r|exists s]; by split.
- move=> [[r s] [_ [_ ht]] [[a [ha ea]] [b [hb eb]]]].
  exists t; split=> //; exists (r,s); split.
  + split; [by rewrite -ea|by rewrite -eb].
  + exact ht.
Qed.

(** Source for [measure_step_sum_fibre_grouping]: the grouping sum over
    r+s=t in Federer 2.4.1, p. 81 *)
Theorem measure_step_sum_fibre_grouping (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u v : partial_function X (real_line_metric R)) :
  is_measure_measurable_function mu u -> is_measure_measurable_function mu v ->
  countable (partial_function_range u) -> countable (partial_function_range v) ->
  forall t : R,
    nonnegative_sum [set p : R * R | (p.1+p.2)%R=t] (measure_step_joint_fibre mu u v) =
      mu (partial_function_preimage (partial_real_function_add u v) [set t]).
Proof.
move=> hu hv hcu hcv t.
pose A := [set p : R * R | (p.1+p.2)%R=t].
pose D := partial_function_range u `*` partial_function_range v.
pose F (p : R * R) := partial_function_preimage u [set p.1] `&` partial_function_preimage v [set p.2].
have hc : countable (A `&` D).
  apply: sub_countable _ (@countableX _ _ _ _ hcu hcv).
  apply: subset_card_le=> p [_ hp]; exact hp.
have hF p : (A `&` D) p -> measure_measurable mu (F p).
  move=> _; exact (@measure_measurable_intersection R X mu hm _ _
    (@measurable_real_fibre R X mu hm u hu p.1) (@measurable_real_fibre R X mu hm v hv p.2)).
have hd p q : (A `&` D) p -> (A `&` D) q -> p != q ->
    forall x, F p x -> F q x -> False.
  move=> hp hq hne x [[a [ha ea]] [b [hb eb]]] [[c [hgc ec]] [d [hgd ed]]].
  have e1 := partial_function_single_valued ha hgc.
  have e2 := partial_function_single_valued hb hgd.
  apply: (negP hne); apply/eqP; apply: injective_projections.
  - by rewrite -ea -ec.
  - by rewrite -eb -ed.
have he : (\bigcup_(p in A `&` D) F p) = partial_function_preimage (partial_real_function_add u v) [set t].
  rewrite partial_real_sum_fibre_union; apply/seteqP; split=> x [p hp hx]; exists p=> //.
  - have [ht [hpu hpv]] := hp; by split=> //; split.
  - have [hpu [hpv ht]] := hp; by split=> //; split.
have hs := @measure_countable_disjoint_additivity R X [the choiceType of (R*R)%type] mu hm
  (A `&` D) F hc hF hd.
rewrite he in hs; rewrite hs.
have hp p : A p -> 0 <= measure_step_joint_fibre mu u v p by move=> _; exact: measure_nonnegative.
have hz : nonnegative_sum (A `\` D) (measure_step_joint_fibre mu u v) = 0.
  apply: nonnegative_sum_zero=> p hmem; case: p hmem=> r s [_ hn].
  have hnot : ~ partial_function_range u r \/ ~ partial_function_range v s.
    case: (pselect (partial_function_range u r))=> hr; last by left.
    right=> hv'; apply: hn; by split.
  rewrite /measure_step_joint_fibre /=.
  case: hnot=> hn'; rewrite (partial_fibre_outside_range hn') ?set0I ?setI0; exact: measure_empty.
by rewrite (nonnegative_sum_split D hp) hz adde0.
Qed.
