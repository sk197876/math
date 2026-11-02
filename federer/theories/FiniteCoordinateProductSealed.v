(** Sealed finite products for Federer (1969), 2.6.6, p. 120. Only the
    abstract recursion and consistency laws are exposed; the point choice
    and coordinate-fold implementation remain private. Source context:
    CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP MonotoneDaniellIntegralUP
  FiniteCoordinateProductUP FiniteCoordinateProductConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Module Type FiniteCoordinateProductSignature.
(** Source for [value]: the family of finite product integrals in
    Federer 2.6.6, p. 120. *)
Parameter value : forall (R : realType) (I : choiceType) (Y : I -> topologicalType)
  (A : forall i, (Y i -> R) -> R),
  (forall i, hausdorff_space (Y i)) -> (forall i, compact (@setT (Y i))) ->
  (forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i)) ->
  (forall i, A i (fun _=>1) = 1) -> {fset I} -> (prod_topology Y -> R) -> R.
(** Source for [laws]: the finite-product recursion and consistency
    laws in Federer 2.6.6, p. 120. *)
Parameter laws : forall (R : realType) (I : choiceType) (Y : I -> topologicalType)
  (A : forall i, (Y i -> R) -> R)
  (hh : forall i, hausdorff_space (Y i)) (hc : forall i, compact (@setT (Y i)))
  (hA : forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i))
  (hA1 : forall i, A i (fun _=>1) = 1),
  is_finite_coordinate_product_family A (@value R I Y A hh hc hA hA1).
End FiniteCoordinateProductSignature.
Module FiniteCoordinateProduct : FiniteCoordinateProductSignature.
(** Source for [value]: private selection of a proved finite-product
    family, Federer 2.6.6, p. 120. *)
Definition value (R : realType) (I : choiceType) (Y : I -> topologicalType)
  (A : forall i, (Y i -> R) -> R)
  (hh : forall i, hausdorff_space (Y i)) (hc : forall i, compact (@setT (Y i)))
  (hA : forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i))
  (hA1 : forall i, A i (fun _=>1) = 1) :=
  sval (cid (@finite_coordinate_product_family_exists R I Y A hh hc hA hA1)).
(** Source for [laws]: verification of the selected finite family,
    Federer 2.6.6, p. 120. *)
Lemma laws (R : realType) (I : choiceType) (Y : I -> topologicalType)
  (A : forall i, (Y i -> R) -> R)
  (hh : forall i, hausdorff_space (Y i)) (hc : forall i, compact (@setT (Y i)))
  (hA : forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i))
  (hA1 : forall i, A i (fun _=>1) = 1) :
  is_finite_coordinate_product_family A (@value R I Y A hh hc hA hA1).
Proof. exact: svalP (cid (@finite_coordinate_product_family_exists R I Y A hh hc hA hA1)). Qed.
End FiniteCoordinateProduct.
