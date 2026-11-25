(** Federer (1969), 2.10.28, p. 193: bounds, monotonicity and increment
    values of the finite cumulative function. These consequences use its
    half-line specification alone. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic FiniteMeasureSetDifference FiniteCumulativeFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_cumulative_function_bounds]: supporting
    0<=f(x)<=total mass in 2.10.28, p. 193,
    before proving all intermediate values occur. *)
Lemma finite_cumulative_function_bounds (R : realType) (mu : set R -> \bar R)
    (hm : is_measure mu) (f : R -> R) (hf : is_finite_cumulative_function mu f) c :
  mu setT=c%:E -> forall x, 0<=f x /\ f x<=c.
Proof.
move=> hc x; split.
- have hh := measure_nonnegative hm [set z | z<=x].
  by rewrite (hf x) lee_fin in hh.
- have hh := @measure_mono R R mu hm [set z | z<=x] setT (fun _ _=>Logic.I).
  by rewrite (hf x) hc lee_fin in hh.
Qed.

(** Source for [finite_cumulative_function_nondecreasing]: direct f(b)>=f(a)
    for a<=b in 2.10.28, p. 193. Half-line containment suffices. *)
Lemma finite_cumulative_function_nondecreasing (R : realType) (mu : set R -> \bar R)
    (hm : is_measure mu) (f : R -> R) (hf : is_finite_cumulative_function mu f) a b :
  a<=b -> f a<=f b.
Proof.
move=> hab; have hh : (mu [set z : R | (z<=a)%R]<=mu [set z : R | (z<=b)%R])%E.
  apply: (@measure_mono R R mu hm)=> z hza; exact: le_trans hza hab.
by rewrite (hf a) (hf b) lee_fin in hh.
Qed.

(** Source for [finite_cumulative_function_increment]: supporting
    f(b)-f(a)=mu((a,b]) in 2.10.28, p. 193,
    using the exact closed-half-line convention.
    State the interval as the difference of
    rays; a<=b and measurability of the
    lower ray suffice, without atomlessness. *)
Lemma finite_cumulative_function_increment (R : realType) (mu : set R -> \bar R)
    (hm : is_measure mu) (f : R -> R) (hf : is_finite_cumulative_function mu f) a b :
  a<=b -> measure_measurable mu [set z | z<=a] ->
  mu ([set z | z<=b] `\` [set z | z<=a])=(f b-f a)%:E.
Proof.
move=> hab hmeas.
apply: (@finite_measure_nested_difference R R mu hm _ _ (f a) (f b) hmeas _ (hf a) (hf b)).
move=> z hza; exact: le_trans hza hab.
Qed.
