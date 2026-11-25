(** Federer (1969), 2.10.28, p. 193: existence witness for the real
    cumulative function of a finite measure. The finite-part implementation
    is hidden by the sealing module. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic FiniteCumulativeFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_cumulative_function_exists]: supporting
    existence of the real f defined in
    2.10.28, p. 193. Monotonicity bounds
    every half-line value by the finite
    total mass. No arbitrary infinite-value
    convention is exposed to later proofs. *)
Theorem finite_cumulative_function_exists (R : realType) (mu : set R -> \bar R)
    (hm : is_measure mu) : mu setT< +oo -> exists f, is_finite_cumulative_function mu f.
Proof.
move=> hfin; exists (fun x=>fine (mu [set z | (z<=x)%R]))=> x.
symmetry; apply: fineK; rewrite (ge0_fin_numE (measure_nonnegative hm _)).
apply: le_lt_trans _ hfin; apply: (@measure_mono R R mu hm _ setT); by [].
Qed.
