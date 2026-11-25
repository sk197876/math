(** Private existence proof for the norm in Federer (1969), 2.5.19, p. 113,
    supporting 2.6.6, p. 120. A maximum on the compact support gives the
    least bound; no maximum is exposed downstream. Source context and
    empty-domain convention: UniformFunctionNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From mathcomp.analysis.normedtype_theory Require Import pseudometric_normed_Zmodule.
From Federer Require Import RealMetricBackground CompactSupportFunctionUP CompactMaximum UniformFunctionNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_support_uniform_norm_exists]: supporting
    existence of nu from Federer 2.5.19, p. 113. The same definition
    works for compactly supported functions without compactness of X;
    this is a stated strengthening of the compact-space application. *)
Theorem compact_support_uniform_norm_exists (R : realType) (X : topologicalType) (f : X -> R) :
  compactly_supported_continuous_functions f -> exists n, is_uniform_function_norm f n.
Proof.
move=> [hf hK]; case: (pselect (real_function_support f !=set0))=> hne.
- have hn : continuous (fun x : X => (`|f x| : R^o)).
    move=> x; exact: continuous_comp (hf x) (@norm_continuous R R^o _).
  have [x [hx hb]] := @continuous_compact_maximum R X (real_function_support f) _ hne hK hn.
  exists (`|f x|); constructor; first exact: normr_ge0.
  + move=> y; case: (pselect (real_function_support f y))=> hy; first exact: hb y hy.
    rewrite (real_function_zero_off_support hy) normr0; exact: normr_ge0.
  + by move=> c hc hfc; exact: hfc.
- exists 0; constructor=> // x.
  have hx : ~real_function_support f x by move=> hx; apply: hne; exists x.
  by rewrite (real_function_zero_off_support hx) normr0.
Qed.
