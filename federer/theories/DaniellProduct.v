(** Public product Daniell functional for Federer (1969), 2.6.4,
    p. 119. Existence is sealed; uniqueness and the separated-
    product diagram are proved through the abstract laws. Source
    editions and the corrected last assertion are in DaniellProductUP.v. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP DaniellIntegralUP DaniellProductUP DaniellProductSealed DaniellProductUniqueness IteratedCompactDaniell IteratedCompactFunctionalAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
(** Source for [daniell_product]: public product functional in
    the last proposition of Federer 2.6.4, p. 119. *)
Definition daniell_product (R : realType) (X Y : topologicalType)
    (A : (X -> R) -> R) (B : (Y -> R) -> R)
    (hX : hausdorff_space X) (hlX : locally_compact (@setT X))
    (hY : hausdorff_space Y) (hlY : locally_compact (@setT Y))
    (hA : is_daniell_integral (@compactly_supported_continuous_functions R X) A)
    (hB : is_daniell_integral (@compactly_supported_continuous_functions R Y) B) :=
  @DaniellProduct.value R X Y A B hX hlX hY hlY hA hB.

(** Source for [daniell_product_specification]: Daniell laws and
    the final diagram of Federer 2.6.4, p. 119. *)
Lemma daniell_product_specification (R : realType) (X Y : topologicalType)
    (A : (X -> R) -> R) (B : (Y -> R) -> R)
    (hX : hausdorff_space X) (hlX : locally_compact (@setT X))
    (hY : hausdorff_space Y) (hlY : locally_compact (@setT Y))
    (hA : is_daniell_integral (@compactly_supported_continuous_functions R X) A)
    (hB : is_daniell_integral (@compactly_supported_continuous_functions R Y) B) :
  is_daniell_product A B (@daniell_product R X Y A B hX hlX hY hlY hA hB).
Proof. exact: DaniellProduct.laws. Qed.

(** Source for [daniell_product_iterated_value]: supporting iterated
    formula for the unique product in Federer 2.6.4, p. 119.
    It follows from uniqueness, without unfolding the sealed value. *)
Lemma daniell_product_iterated_value (R : realType) (X Y : topologicalType)
    (A : (X -> R) -> R) (B : (Y -> R) -> R)
    (hX : hausdorff_space X) (hlX : locally_compact (@setT X))
    (hY : hausdorff_space Y) (hlY : locally_compact (@setT Y))
    (hA : is_daniell_integral (@compactly_supported_continuous_functions R X) A)
    (hB : is_daniell_integral (@compactly_supported_continuous_functions R Y) B) (h : (X*Y) -> R) :
  compactly_supported_continuous_functions h ->
  @daniell_product R X Y A B hX hlX hY hlY hA hB h=B (fun y => A (fun x => h (x,y))).
Proof.
move=> hh.
have hJ : is_daniell_product A B (fun h => B (fun y => A (fun x => h (x,y)))).
  split; first exact (@iterated_compact_functional_daniell R X Y A B hX hlX hY hlY hA hB).
  move=> f g hf hg; exact (@iterated_compact_functional_generator R X Y A B f g hA hB hf hg).
exact (@daniell_product_unique R X Y A B _ _ hX hlX hY hlY
  (@daniell_product_specification R X Y A B hX hlX hY hlY hA hB) hJ h hh).
Qed.
