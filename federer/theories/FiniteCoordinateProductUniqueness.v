(** Federer (1969), 2.6.6, p. 120: uniqueness of the finite products used as
    marginals. The proof uses only the abstract empty-product and
    adjoining-factor laws, leaving the coordinate-fold witness private.
    Source context: CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP ProductCylinderLattice ConsistentCylinderFunctionalUP
  FiniteCoordinateProductUP CoordinateDaniellOperator CoordinateDaniellDependence NormalizedProductSpace
  MonotoneDaniellIntegralUP MonotoneDaniellIntegralSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope fset_scope.

(** Source for [finite_coordinate_product_family_unique]: supporting
    uniqueness of the finite marginals in Federer 2.6.6, p. 120,
    by finite-set induction and the binary product law of 2.6.4. *)
Theorem finite_coordinate_product_family_unique (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (A : forall i, (Y i -> R) -> R)
    (C D : {fset I} -> (prod_topology Y -> R) -> R) :
  (forall i, hausdorff_space (Y i)) -> (forall i, compact (@setT (Y i))) ->
  (forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i)) ->
  (forall i, A i (fun _=>1) = 1) ->
  is_finite_coordinate_product_family A C -> is_finite_coordinate_product_family A D ->
  forall F f, continuous_coordinate_functions F f -> C F f=D F f.
Proof.
move=> hh hc hA hA1 hC hD.
have [x0 _] := normalized_daniell_product_nonempty hA hA1.
have hX := compact_factor_product_compact hc.
elim/fset1U_rect=> [|i F hi ih] f hf.
- by rewrite (finite_coordinate_product_empty hC hf x0) (finite_coordinate_product_empty hD hf x0).
- rewrite (finite_coordinate_product_adjoin hC hi hf) (finite_coordinate_product_adjoin hD hi hf).
  apply: ih; split.
  + exact (@coordinate_daniell_operator_preserves_continuity R I Y A i (hh i) (hc i) hX
      (monotone_daniell_integral_is_daniell (hA i)) f hf.1).
  + have hd := @coordinate_daniell_operator_determined R I Y A i (i |` F) f hf.2.
    by rewrite fsetU1K in hd.
Qed.
