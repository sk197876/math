(** Federer (1969), 2.3.3, p. 76: selecting a measurable value according to
    a measurable set preserves measurability. This supports the greedy
    recursion *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  MeasureUP MeasureFiniteClosure MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [measurable_total_piecewise]: supporting measurable
    include-or-omit step for Federer 2.3.3, p. 76,
    obtained from the measurable-set closure laws of 2.1.3. *)
Lemma measurable_total_piecewise (R : realType) (X : choiceType) (Y : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X) (f g : X -> Y) :
  measure_measurable mu A ->
  is_measure_measurable_function mu (partial_function_total f) ->
  is_measure_measurable_function mu (partial_function_total g) ->
  is_measure_measurable_function mu
    (partial_function_total (fun x => if pselect (A x) then f x else g x)).
Proof.
move=> hA hf hg; constructor.
- rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hm.
- move=> U ho; rewrite partial_function_total_preimage.
  have he : (fun x => if pselect (A x) then f x else g x) @^-1` U =
      (A `&` (f @^-1` U)) `|` ((g @^-1` U) `\` A).
    apply/seteqP; split=> x; rewrite /preimage /=; case: (pselect (A x))=> hx.
    + by move=> hu; left; split.
    + by move=> hu; right; split.
    + by move=> [[_ hu]|[_ hn]] //; exact: False_ind (hn hx).
    + by move=> [[ha _]|[hu _]] //; exact: False_ind (hx ha).
  have hfU := @measurable_function_open_preimage R X Y mu _ hf U ho.
  have hgU := @measurable_function_open_preimage R X Y mu _ hg U ho.
  rewrite !partial_function_total_preimage in hfU hgU.
  rewrite he; apply: (@measure_measurable_union R X mu hm).
  + exact: (@measure_measurable_intersection R X mu hm _ _ hA hfU).
  + exact: (@measure_measurable_difference R X mu hm _ _ hgU hA).
Qed.
