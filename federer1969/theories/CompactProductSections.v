(** Federer (1969), 2.6.4, p. 119, final proposition: sections of a
    continuous compactly supported function on X times Y have compact
    support in the factors. These are supporting general topology lemmas for
    the product Daniell functional. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals topology.
From Federer Require Import RealMetricBackground CompactSupportFunctionUP TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_product_first_projection]: supporting
    compact projection of the support in Federer 2.6.4,
    p. 119; this is general topology, not a separate assertion
    of the book. *)
Lemma compact_product_first_projection (X Y : topologicalType) (K : set (X*Y)) :
  compact K -> compact (fst @` K).
Proof.
move=> hK; apply: continuous_compact _ hK.
exact: continuous_subspaceT (@first_projection_continuous X Y).
Qed.

(** Source for [compact_product_second_projection]: supporting
    compact projection of the support for the product functional
    in Federer 2.6.4, p. 119. *)
Lemma compact_product_second_projection (X Y : topologicalType) (K : set (X*Y)) :
  compact K -> compact (snd @` K).
Proof.
move=> hK; apply: continuous_compact _ hK.
exact: continuous_subspaceT (@second_projection_continuous X Y).
Qed.

(** Source for [compact_product_first_section]: supporting membership
    of x maps to h(x,y) in K(X), used to define the
    iterated functional in Federer 2.6.4, p. 119. *)
Lemma compact_product_first_section (R : realType) (X Y : topologicalType)
    (h : (X*Y) -> R) (y : Y) : hausdorff_space X ->
  compactly_supported_continuous_functions h ->
  compactly_supported_continuous_functions (fun x => h (x,y)).
Proof.
move=> hX [hh hK]; split.
- have hc : continuous (fun x : X => (x,y)).
    apply: topological_pair_continuous; [by move=> z|exact: cst_continuous].
  move=> x; exact: continuous_comp (hc x) (hh (x,y)).
- have hproj := compact_product_first_projection hK.
  apply: (@real_function_compact_support_in_closed_set R X _ (fst @` real_function_support h)
    hproj (compact_closed hX hproj))=> x hx.
  apply: real_function_zero_off_support=> hp; apply: hx.
  exists (x,y)=> //.
Qed.

(** Source for [compact_product_second_section]: supporting membership
    of y maps to h(x,y) in K(Y), for Federer 2.6.4,
    p. 119. No nonempty-space hypothesis is introduced. *)
Lemma compact_product_second_section (R : realType) (X Y : topologicalType)
    (h : (X*Y) -> R) (x : X) : hausdorff_space Y ->
  compactly_supported_continuous_functions h ->
  compactly_supported_continuous_functions (fun y => h (x,y)).
Proof.
move=> hY [hh hK]; split.
- have hc : continuous (fun y : Y => (x,y)).
    apply: topological_pair_continuous; [exact: cst_continuous|by move=> z].
  move=> y; exact: continuous_comp (hc y) (hh (x,y)).
- have hproj := compact_product_second_projection hK.
  apply: (@real_function_compact_support_in_closed_set R Y _ (snd @` real_function_support h)
    hproj (compact_closed hY hproj))=> y hy.
  apply: real_function_zero_off_support=> hp; apply: hy.
  exists (x,y)=> //.
Qed.
