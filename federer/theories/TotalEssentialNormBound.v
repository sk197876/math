(** Federer (1969), 2.5.8, p. 100: uniformly bounded representatives used to
    bound the operator seminorm. These adapters expose the existing abstract
    essential norm. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  PartialFunctionUP MeasureEssentialNormUP MeasureEssentialNorm MeasureEssentialNormAttainment
  TotalScalarLpUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_essential_norm_bound]: supporting almost bound in
    Federer 2.5.8, p. 100 No finiteness of mu(X) or countable measurability
    of X is assumed. *)
Lemma total_essential_norm_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> R) (b : R) :
  (0 <= b)%R -> measure_almost_everywhere mu [set x | (`|f x| <= b)%R] ->
  total_scalar_lp_norm mu +oo f <= b%:E.
Proof.
move=> hb ha; apply: measure_essential_norm_bound; split; first by rewrite lee_fin.
apply: (@measure_null_subset R X mu hm _ _ _ ha)=> x [y [hy hby]] hx.
have he : f x=y := hy.
have hh : (`|y| <= b)%R by rewrite -he.
change (is_true (b%:E < (`|y|%R)%:E)) in hby.
rewrite lte_fin in hby; by have := lt_le_trans hby hh; rewrite ltxx.
Qed.

(** Source for [total_essential_norm_almost_bound]: attained bound used in
    Federer 2.5.8, p. 100 *)
Lemma total_essential_norm_almost_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> R) (b : R) :
  total_scalar_lp mu +oo f -> total_scalar_lp_norm mu +oo f <= b%:E ->
  measure_almost_everywhere mu [set x | (`|f x| <= b)%R].
Proof.
move=> hf hb.
have hd : measure_almost_everywhere mu (partial_function_domain (total_scalar_function f)).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
  by move=> x _; exists (f x).
have ha := @measure_essential_norm_almost_bound R X R mu hm
  (fun y : R => `|y|%R) (total_scalar_function f) hd.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ ha)=> x [y [hy hby]].
have he : f x=y := hy.
have hh := le_trans hby hb; rewrite lee_fin -he in hh; exact: hh.
Qed.
