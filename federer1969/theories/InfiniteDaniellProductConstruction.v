(** Private existence proof of Federer's infinite product, 2.6.6, p. 120.
    Actual finite products, their consistency, cylinder density, and the
    norm-bounded extension are all proved separately. The only input
    integrals are the factors given in the book. Source context:
    CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP MonotoneDaniellIntegralUP NormalizedProductSpace
  FiniteCoordinateProductUP FiniteCoordinateProduct InfiniteDaniellProductUP CylinderDaniellExtensionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [infinite_daniell_product_exists]: existence of the
    normalized monotone product functional in Federer 2.6.6, p. 120,
    with all the prescribed finite marginals. The inverse-limit
    generalization on pp. 120–121 is a separate statement. *)
Theorem infinite_daniell_product_exists (R : realType) (I : choiceType) (Y : I -> topologicalType)
  (A : forall i, (Y i -> R) -> R)
  (hh : forall i, hausdorff_space (Y i)) (hc : forall i, compact (@setT (Y i)))
  (hA : forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i))
  (hA1 : forall i, A i (fun _=>1) = 1) :
  exists B, is_infinite_daniell_product hh hc hA hA1 B.
Proof.
have [x0 _] := normalized_daniell_product_nonempty hA hA1.
have hC := finite_coordinate_product_specification hh hc hA hA1.
exact: (@cylinder_daniell_extension_exists R I Y x0 _ (hausdorff_factor_product_hausdorff hh)
  (compact_factor_product_compact hc) (finite_coordinate_product_consistency hC)).
Qed.
