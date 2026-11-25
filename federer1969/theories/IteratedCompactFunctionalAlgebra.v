(** Federer (1969), 2.6.4, p. 119: algebraic laws of the iterated candidate
    for the product Daniell functional. The candidate is expressed directly
    in terms of the two given functionals; the public product will be
    specified and sealed separately. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionUP CompactSupportFunctionLattice CompactProductSections
  CompactSectionFunctional DaniellIntegralUP FunctionLatticeUP FunctionLatticeSeminormUP DaniellSpaceCompactness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [iterated_compact_functional_linear]: supporting
    linearity of the product functional in Federer 2.6.4,
    p. 119. All real scalar multiples are included. *)
Theorem iterated_compact_functional_linear (R : realType) (X Y : topologicalType)
    (A : (X -> R) -> R) (B : (Y -> R) -> R) :
  hausdorff_space X -> locally_compact (@setT X) -> hausdorff_space Y ->
  is_daniell_integral (@compactly_supported_continuous_functions R X) A ->
  is_daniell_integral (@compactly_supported_continuous_functions R Y) B ->
  is_linear_functional_on_functions (@compactly_supported_continuous_functions R (X*Y)%type)
    (fun h => B (fun y => A (fun x => h (x,y)))).
Proof.
move=> hX hlX hY hA hB.
have hlinA := @daniell_compact_support_linear R X A hA.
have hlinB := @daniell_compact_support_linear R Y B hB.
split.
- move=> f g hf hg.
  have he : (fun y => A (fun x => f (x,y)+g (x,y)))=
      (fun y => A (fun x => f (x,y))+A (fun x => g (x,y))).
    apply: funext=> y; exact (hlinA.1 _ _
      (@compact_product_first_section R X Y f y hX hf) (@compact_product_first_section R X Y g y hX hg)).
  rewrite he; exact (hlinB.1 _ _
    (@compact_section_functional_compact_support R X Y A f hX hlX hY hA hf)
    (@compact_section_functional_compact_support R X Y A g hX hlX hY hA hg)).
- move=> c f hf.
  have he : (fun y => A (fun x => c*f (x,y)))=(fun y => c*A (fun x => f (x,y))).
    apply: funext=> y; exact (hlinA.2 c _ (@compact_product_first_section R X Y f y hX hf)).
  rewrite he; exact (hlinB.2 c _ (@compact_section_functional_compact_support R X Y A f hX hlX hY hA hf)).
Qed.

(** Source for [iterated_compact_functional_generator]: the final
    diagram on elementary tensors in Federer 2.6.4, p. 119.
    This is valid for arbitrary signed Daniell functionals. *)
Lemma iterated_compact_functional_generator (R : realType) (X Y : topologicalType)
    (A : (X -> R) -> R) (B : (Y -> R) -> R) (f : X -> R) (g : Y -> R) :
  is_daniell_integral (@compactly_supported_continuous_functions R X) A ->
  is_daniell_integral (@compactly_supported_continuous_functions R Y) B ->
  compactly_supported_continuous_functions f -> compactly_supported_continuous_functions g ->
  B (fun y => A (fun x => f x*g y))=A f*B g.
Proof.
move=> hA hB hf hg.
have hlinA := @daniell_compact_support_linear R X A hA.
have hlinB := @daniell_compact_support_linear R Y B hB.
have he : (fun y => A (fun x => f x*g y))=(fun y => A f*g y).
  apply: funext=> y; rewrite (funext (fun x => mulrC (f x) (g y))) (hlinA.2 (g y) f hf) mulrC; by [].
rewrite he; exact: hlinB.2 (A f) g hg.
Qed.
