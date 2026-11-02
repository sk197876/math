(** Federer (1969), 2.6.4, p. 119: boundedness of compactly supported
    continuous functions, supporting the order bounds for the product
    Daniell functional. This is general topology, also used in 2.5.13, pp.
    106–107. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From mathcomp.analysis.normedtype_theory Require Import pseudometric_normed_Zmodule.
From Federer Require Import RealMetricBackground CompactSupportFunctionUP CompactMaximum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_support_uniform_bound]: supporting finite
    bound for every f in K(X), in Federer 2.6.4,
    p. 119. Empty supports and empty spaces are included. *)
Lemma compact_support_uniform_bound (R : realType) (X : topologicalType) (f : X -> R) :
  compactly_supported_continuous_functions f -> exists M, 0<=M /\ forall x, `|f x|<=M.
Proof.
move=> [hf hK]; case: (pselect (real_function_support f !=set0))=> hne.
- have hn : continuous (fun x : X => (`|f x| : R^o)).
    move=> x; exact: continuous_comp (hf x) (@norm_continuous R R^o _).
  have [x [hx hb]] := @continuous_compact_maximum R X (real_function_support f) _ hne hK hn.
  exists (`|f x|); split; first exact: normr_ge0.
  move=> y; case: (pselect (real_function_support f y))=> hy; first exact: hb y hy.
  rewrite (real_function_zero_off_support hy) normr0; exact: normr_ge0.
- exists 0; split; first exact: lexx.
  move=> x; have hx : ~real_function_support f x by move=> hx; apply: hne; exists x.
  by rewrite (real_function_zero_off_support hx) normr0.
Qed.
