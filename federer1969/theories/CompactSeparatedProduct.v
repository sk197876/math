(** Federer (1969), 2.6.4, p. 119: the top arrow K(X) tensor K(Y) to K(X
    times Y) sends f tensor g to f(x)g(y). This module proves the
    compact-support membership needed for that arrow. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From mathcomp.analysis.normedtype_theory Require Import normed_module.
From Federer Require Import RealMetricBackground TopologicalProductMaps CompactSupportFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compactly_supported_separated_product]: membership
    of separated products in K(X times Y), required by the
    final diagram in Federer 2.6.4, p. 119. *)
Theorem compactly_supported_separated_product (R : realType) (X Y : topologicalType)
    (f : X -> R) (g : Y -> R) :
  compactly_supported_continuous_functions f -> compactly_supported_continuous_functions g ->
  compactly_supported_continuous_functions (fun p : X*Y => f p.1*g p.2).
Proof.
move=> hf hg; split.
- move=> p; apply: (@continuousM R (X*Y)%type _ _ p).
  + exact: continuous_comp (@first_projection_continuous X Y p) (hf.1 p.1).
  + exact: continuous_comp (@second_projection_continuous X Y p) (hg.1 p.2).
- apply: (@real_function_compact_support_in_closed_set R (X*Y)%type _
    (real_function_support f `*` real_function_support g)).
  + exact: compact_setX hf.2 hg.2.
  + apply: closedI.
    * exact ((continuous_closedP (@fst X Y)).1 (@first_projection_continuous X Y) _ (@real_function_support_closed R X f)).
    * exact ((continuous_closedP (@snd X Y)).1 (@second_projection_continuous X Y) _ (@real_function_support_closed R Y g)).
  + move=> [x y] hnot; case: (pselect (real_function_support f x))=> hx.
    * have hy : ~real_function_support g y by move=> hy; apply: hnot; split.
      by rewrite (real_function_zero_off_support hy) mulr0.
    * by rewrite (real_function_zero_off_support hx) mul0r.
Qed.
