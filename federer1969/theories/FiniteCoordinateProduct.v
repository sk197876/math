(** Public finite-product family for Federer (1969), 2.6.6, p. 120. Only the
    sealed recursion and consistency laws are used downstream; Source
    context: CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP MonotoneDaniellIntegralUP
  FiniteCoordinateProductUP FiniteCoordinateProductSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_coordinate_product]: the family of finite
    marginals in Federer 2.6.6, p. 120, exposed abstractly. *)
Definition finite_coordinate_product (R : realType) (I : choiceType) (Y : I -> topologicalType)
  (A : forall i, (Y i -> R) -> R)
  (hh : forall i, hausdorff_space (Y i)) (hc : forall i, compact (@setT (Y i)))
  (hA : forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i))
  (hA1 : forall i, A i (fun _=>1) = 1) :=
  @FiniteCoordinateProduct.value R I Y A hh hc hA hA1.

(** Source for [finite_coordinate_product_specification]: the
    abstract defining laws of finite products, Federer 2.6.6, p. 120. *)
Lemma finite_coordinate_product_specification (R : realType) (I : choiceType) (Y : I -> topologicalType)
  (A : forall i, (Y i -> R) -> R)
  (hh : forall i, hausdorff_space (Y i)) (hc : forall i, compact (@setT (Y i)))
  (hA : forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i))
  (hA1 : forall i, A i (fun _=>1) = 1) :
  is_finite_coordinate_product_family A (@finite_coordinate_product R I Y A hh hc hA hA1).
Proof. exact: (@FiniteCoordinateProduct.laws R I Y A hh hc hA hA1). Qed.
