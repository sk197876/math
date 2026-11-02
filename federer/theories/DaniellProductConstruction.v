(** Private existence witness for Federer (1969), 2.6.4, p. 119: compose the
    given Daniell functionals on continuous compactly supported sections.
    The abstract specification is in DaniellProductUP.v, including Source
    context and the erratum distinction. The construction will be hidden by
    opaque sealing. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP DaniellIntegralUP DaniellProductUP
  IteratedCompactDaniell IteratedCompactFunctionalAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [daniell_product_exists]: existence part of the
    final proposition in Federer 2.6.4, p. 119.
    No positivity is assumed for the given functionals. *)
Theorem daniell_product_exists (R : realType) (X Y : topologicalType)
    (A : (X -> R) -> R) (B : (Y -> R) -> R) :
  hausdorff_space X -> locally_compact (@setT X) -> hausdorff_space Y -> locally_compact (@setT Y) ->
  is_daniell_integral (@compactly_supported_continuous_functions R X) A ->
  is_daniell_integral (@compactly_supported_continuous_functions R Y) B ->
  exists C, is_daniell_product A B C.
Proof.
move=> hX hlX hY hlY hA hB.
exists (fun h => B (fun y => A (fun x => h (x,y)))); split.
- exact (@iterated_compact_functional_daniell R X Y A B hX hlX hY hlY hA hB).
- move=> f g hf hg; exact (@iterated_compact_functional_generator R X Y A B f g hA hB hf hg).
Qed.
