(** Federer (1969), 2.6.4, p. 119: the monotone case of the final
    product-functional proposition. Positivity/order preservation is
    inherited by the iterated functional. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionUP CompactProductSections CompactSectionFunctional
  DaniellIntegralUP MonotoneDaniellIntegralUP MonotoneDaniellIntegralSum DaniellProductUP DaniellProductUniqueness
  IteratedCompactDaniell IteratedCompactFunctionalAlgebra FunctionLatticeUP ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [daniell_product_is_monotone]: the monotone
    specialization of the product in Federer 2.6.4, p. 119.
    This is separate from the corrected measure-representation formula. *)
Theorem daniell_product_is_monotone (R : realType) (X Y : topologicalType)
    (A : (X -> R) -> R) (B : (Y -> R) -> R) (C : ((X*Y) -> R) -> R) :
  hausdorff_space X -> locally_compact (@setT X) -> hausdorff_space Y -> locally_compact (@setT Y) ->
  is_monotone_daniell_integral (@compactly_supported_continuous_functions R X) A ->
  is_monotone_daniell_integral (@compactly_supported_continuous_functions R Y) B ->
  is_daniell_product A B C -> is_monotone_daniell_integral (@compactly_supported_continuous_functions R (X*Y)%type) C.
Proof.
move=> hX hlX hY hlY hA hB hC.
have hAd := monotone_daniell_integral_is_daniell hA.
have hBd := monotone_daniell_integral_is_daniell hB.
have hJ : is_daniell_product A B (fun h => B (fun y => A (fun x => h (x,y)))).
  split; first exact (@iterated_compact_functional_daniell R X Y A B hX hlX hY hlY hAd hBd).
  move=> f g hf hg; exact (@iterated_compact_functional_generator R X Y A B f g hAd hBd hf hg).
have hval f hf := @daniell_product_unique R X Y A B C _ hX hlX hY hlY hC hJ f hf.
have hmono f g : compactly_supported_continuous_functions f -> compactly_supported_continuous_functions g ->
    function_le f g -> C f<=C g.
  move=> hf hg hfg; rewrite (hval f hf) (hval g hg).
  apply: (@monotone_daniell_integral_monotone R Y _ B hB _ _
    (@compact_section_functional_compact_support R X Y A f hX hlX hY hAd hf)
    (@compact_section_functional_compact_support R X Y A g hX hlX hY hAd hg))=> y.
  exact (@monotone_daniell_integral_monotone R X _ A hA _ _
    (@compact_product_first_section R X Y f y hX hf) (@compact_product_first_section R X Y g y hX hg)
    (fun x => hfg (x,y))).
constructor.
- exact: daniell_integral_add hC.1.
- exact: daniell_integral_scale hC.1.
- exact: hmono.
- move=> f g hf hg hi; split.
  + move=> n m hnm; rewrite lee_fin; apply: (@hmono (f n) (f m) (hf n) (hf m))=> p.
    exact: (hi p).1 n m hnm.
  + exact (@daniell_integral_increasing_continuity R (X*Y)%type _ C hC.1 f g hf hg hi).
Qed.
