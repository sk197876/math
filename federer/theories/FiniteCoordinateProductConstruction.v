(** Private existence proof of the finite-product family for Federer (1969),
    2.6.6, p. 120. Coordinate folds are used only as witnesses of the
    abstract recursion and consistency laws. Source context:
    CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP ProductCylinderLattice ConsistentCylinderFunctionalUP
  FiniteCoordinateProductUP FiniteCoordinateFunctionalConstruction CoordinateDaniellFoldConstruction
  CoordinateDaniellFoldDependenceConstruction CoordinateDaniellOperator
  NormalizedProductSpace MonotoneDaniellIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope fset_scope.

(** Source for [finite_coordinate_product_fold_laws]: the successive
    integration witness satisfies the finite-product specification of
    Federer 2.6.6, p. 120, independently of enumeration order. *)
Lemma finite_coordinate_product_fold_laws (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (A : forall i, (Y i -> R) -> R) (x0 : prod_topology Y) :
  (forall i, hausdorff_space (Y i)) -> (forall i, compact (@setT (Y i))) ->
  (forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i)) ->
  (forall i, A i (fun _=>1) = 1) ->
  is_finite_coordinate_product_family A (finite_coordinate_functional A x0).
Proof.
move=> hh hc hA hA1; have hX := compact_factor_product_compact hc.
constructor.
- exact: finite_coordinate_functional_family hh hc hX hA hA1.
- move=> f [hf hdep] x.
  rewrite (@finite_coordinate_functional_independent R I Y A fset0 f x0 x hdep).
  by rewrite /finite_coordinate_functional /=.
- move=> i F hi f hf.
  have hp : perm_eq (enum_fset (i |` F)) (enum_fset F ++ [:: i]).
    apply: uniq_perm; first exact: fset_uniq.
    + by rewrite cats1 rcons_uniq hi fset_uniq.
    + by move=> j; rewrite mem_cat in_fset1U in_cons in_nil orbF orbC.
  rewrite /finite_coordinate_functional (@coordinate_daniell_fold_permutation R I Y A hh hc hX hA _ _ f hf.1 hp)
    foldr_cat /=; by [].
Qed.

(** Source for [finite_coordinate_product_family_exists]: proved
    existence of all finite products in Federer 2.6.6, p. 120,
    from the given normalized monotone factor integrals. *)
Theorem finite_coordinate_product_family_exists (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (A : forall i, (Y i -> R) -> R) :
  (forall i, hausdorff_space (Y i)) -> (forall i, compact (@setT (Y i))) ->
  (forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i)) ->
  (forall i, A i (fun _=>1) = 1) -> exists C, is_finite_coordinate_product_family A C.
Proof.
move=> hh hc hA hA1; have [x0 _] := normalized_daniell_product_nonempty hA hA1.
exists (finite_coordinate_functional A x0); exact: finite_coordinate_product_fold_laws hh hc hA hA1.
Qed.
