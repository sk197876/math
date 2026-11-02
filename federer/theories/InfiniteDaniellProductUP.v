(** Federer (1969), 2.6.6, p. 120: infinite products of normalized monotone
    Daniell functionals on compact Hausdorff spaces. The object is specified
    by its Daniell laws and all finite marginals, with no coordinate-fold
    construction exposed. Source context: CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP MonotoneDaniellIntegralUP
  FiniteCoordinateProduct CylinderDaniellExtensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_infinite_daniell_product]: the marginal
    characterization of the product in Federer 2.6.6, p. 120.
    The statement also permits finite or empty index sets, a
    boundary-case strengthening of the printed infinite-J hypothesis. *)
Definition is_infinite_daniell_product (R : realType) (I : choiceType) (Y : I -> topologicalType)
  (A : forall i, (Y i -> R) -> R)
  (hh : forall i, hausdorff_space (Y i)) (hc : forall i, compact (@setT (Y i)))
  (hA : forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i))
  (hA1 : forall i, A i (fun _=>1) = 1) (B : (prod_topology Y -> R) -> R) :=
  is_cylinder_daniell_extension (@finite_coordinate_product R I Y A hh hc hA hA1) B.
