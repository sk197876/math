(** Sealed infinite product for Federer (1969), 2.6.6, p. 120. Only the
    normalized Daniell and finite-marginal laws are exposed. The
    dense-extension witness remains private. Source context:
    CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP MonotoneDaniellIntegralUP InfiniteDaniellProductUP InfiniteDaniellProductConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Module Type InfiniteDaniellProductSignature.
(** Source for [value]: the product functional of Federer 2.6.6,
    p. 120. *)
Parameter value : forall (R : realType) (I : choiceType) (Y : I -> topologicalType)
  (A : forall i, (Y i -> R) -> R),
  (forall i, hausdorff_space (Y i)) -> (forall i, compact (@setT (Y i))) ->
  (forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i)) ->
  (forall i, A i (fun _=>1) = 1) -> (prod_topology Y -> R) -> R.
(** Source for [laws]: the defining marginal laws of the product,
    Federer 2.6.6, p. 120. *)
Parameter laws : forall (R : realType) (I : choiceType) (Y : I -> topologicalType)
  (A : forall i, (Y i -> R) -> R)
  (hh : forall i, hausdorff_space (Y i)) (hc : forall i, compact (@setT (Y i)))
  (hA : forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i))
  (hA1 : forall i, A i (fun _=>1) = 1),
  is_infinite_daniell_product hh hc hA hA1 (@value R I Y A hh hc hA hA1).
End InfiniteDaniellProductSignature.
Module InfiniteDaniellProduct : InfiniteDaniellProductSignature.
(** Source for [value]: private choice of the proved product
    functional, Federer 2.6.6, p. 120. *)
Definition value (R : realType) (I : choiceType) (Y : I -> topologicalType)
  (A : forall i, (Y i -> R) -> R)
  (hh : forall i, hausdorff_space (Y i)) (hc : forall i, compact (@setT (Y i)))
  (hA : forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i))
  (hA1 : forall i, A i (fun _=>1) = 1) :=
  sval (cid (@infinite_daniell_product_exists R I Y A hh hc hA hA1)).
(** Source for [laws]: the selected product satisfies its abstract
    laws, Federer 2.6.6, p. 120. *)
Lemma laws (R : realType) (I : choiceType) (Y : I -> topologicalType)
  (A : forall i, (Y i -> R) -> R)
  (hh : forall i, hausdorff_space (Y i)) (hc : forall i, compact (@setT (Y i)))
  (hA : forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i))
  (hA1 : forall i, A i (fun _=>1) = 1) :
  is_infinite_daniell_product hh hc hA hA1 (@value R I Y A hh hc hA hA1).
Proof. exact: svalP (cid (@infinite_daniell_product_exists R I Y A hh hc hA hA1)). Qed.
End InfiniteDaniellProduct.
