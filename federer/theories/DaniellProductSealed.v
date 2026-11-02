(** Opaque product Daniell functional for Federer (1969), 2.6.4,
    p. 119. The abstract laws and source conventions are in
    DaniellProductUP.v. The section-composition witness is private. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP DaniellIntegralUP DaniellProductUP DaniellProductConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Module Type DaniellProductSignature.
(** Source for [value]: the product functional in Federer 2.6.4,
    p. 119, final proposition. *)
Parameter value : forall (R : realType) (X Y : topologicalType)
    (A : (X -> R) -> R) (B : (Y -> R) -> R)
    (hX : hausdorff_space X) (hlX : locally_compact (@setT X))
    (hY : hausdorff_space Y) (hlY : locally_compact (@setT Y))
    (hA : is_daniell_integral (@compactly_supported_continuous_functions R X) A)
    (hB : is_daniell_integral (@compactly_supported_continuous_functions R Y) B), ((X*Y) -> R) -> R.
(** Source for [laws]: the Daniell laws and final diagram in
    Federer 2.6.4, p. 119. *)
Parameter laws : forall (R : realType) (X Y : topologicalType)
    (A : (X -> R) -> R) (B : (Y -> R) -> R)
    (hX : hausdorff_space X) (hlX : locally_compact (@setT X))
    (hY : hausdorff_space Y) (hlY : locally_compact (@setT Y))
    (hA : is_daniell_integral (@compactly_supported_continuous_functions R X) A)
    (hB : is_daniell_integral (@compactly_supported_continuous_functions R Y) B),
  is_daniell_product A B (@value R X Y A B hX hlX hY hlY hA hB).
End DaniellProductSignature.
Module DaniellProduct : DaniellProductSignature.
(** Source for [value]: private choice of the proved witness
    for Federer 2.6.4, p. 119. *)
Definition value (R : realType) (X Y : topologicalType)
    (A : (X -> R) -> R) (B : (Y -> R) -> R)
    (hX : hausdorff_space X) (hlX : locally_compact (@setT X))
    (hY : hausdorff_space Y) (hlY : locally_compact (@setT Y))
    (hA : is_daniell_integral (@compactly_supported_continuous_functions R X) A)
    (hB : is_daniell_integral (@compactly_supported_continuous_functions R Y) B) :=
  projT1 (cid (@daniell_product_exists R X Y A B hX hlX hY hlY hA hB)).
(** Source for [laws]: the chosen witness satisfies the product
    specification of Federer 2.6.4, p. 119. *)
Lemma laws (R : realType) (X Y : topologicalType)
    (A : (X -> R) -> R) (B : (Y -> R) -> R)
    (hX : hausdorff_space X) (hlX : locally_compact (@setT X))
    (hY : hausdorff_space Y) (hlY : locally_compact (@setT Y))
    (hA : is_daniell_integral (@compactly_supported_continuous_functions R X) A)
    (hB : is_daniell_integral (@compactly_supported_continuous_functions R Y) B) :
  is_daniell_product A B (@value R X Y A B hX hlX hY hlY hA hB).
Proof. exact: projT2 (cid (@daniell_product_exists R X Y A B hX hlX hY hlY hA hB)). Qed.
End DaniellProduct.
