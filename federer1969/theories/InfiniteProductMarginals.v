(** Federer (1969), 2.6.6, p. 120: the characterization p_a#(mu)=mu_a for
    every finite a. This connects the sealed cylinder specification to the
    actual projection p_a and the Daniell functional on K(X_a). Source
    context: CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP ConsistentCylinderFunctionalUP CylinderDaniellExtensionUP
  FiniteCoordinateProjection FiniteCoordinatePullback FiniteCoordinateMarginal FiniteCoordinateProductUP
  FiniteCoordinateProduct InfiniteDaniellProductUP InfiniteDaniellProduct NormalizedProductSpace MonotoneDaniellIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [cylinder_extension_marginal_characterization]: exact
    equivalence of the cylinder law with the displayed finite-projection
    characterization in Federer 2.6.6, p. 120. *)
Theorem cylinder_extension_marginal_characterization (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (x0 : prod_topology Y)
    (C : {fset I} -> (prod_topology Y -> R) -> R) (B : (prod_topology Y -> R) -> R) :
  compact (@setT (prod_topology Y)) ->
  (is_cylinder_daniell_extension C B <->
    is_monotone_daniell_integral (@compactly_supported_continuous_functions R (prod_topology Y)) B /\
    B (fun _=>1) = 1 /\ forall F (g : finite_coordinate_space Y F -> R),
      compactly_supported_continuous_functions g ->
      B (g \o finite_coordinate_projection (F:=F))=finite_coordinate_marginal C F g).
Proof.
move=> hc; split.
- move=> [hB [hB1 hBC]]; split=> //; split=> // F g hg.
  exact: hBC F _ (finite_coordinate_pullback_membership hc hg).
- move=> [hB [hB1 hm]]; split=> //; split=> // F f hf.
  have [g [hg he]] := (proj1 (@finite_coordinate_cylinder_image R I Y x0 F f hc)) hf.
  rewrite he; exact: hm F g hg.
Qed.

(** Source for [infinite_product_finite_marginal]: the product
    integral has every prescribed finite marginal, Federer 2.6.6,
    p. 120, stated with the original projection map. *)
Theorem infinite_product_finite_marginal (R : realType) (I : choiceType) (Y : I -> topologicalType)
  (A : forall i, (Y i -> R) -> R)
  (hh : forall i, hausdorff_space (Y i)) (hc : forall i, compact (@setT (Y i)))
  (hA : forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i))
  (hA1 : forall i, A i (fun _=>1) = 1) F (g : finite_coordinate_space Y F -> R) :
  compactly_supported_continuous_functions g ->
  @infinite_daniell_product R I Y A hh hc hA hA1 (g \o finite_coordinate_projection (F:=F))=
    finite_coordinate_marginal (@finite_coordinate_product R I Y A hh hc hA hA1) F g.
Proof.
move=> hg; have hs := @infinite_daniell_product_specification R I Y A hh hc hA hA1.
exact: hs.2.2 F _ (finite_coordinate_pullback_membership (compact_factor_product_compact hc) hg).
Qed.

(** Source for [infinite_product_marginal_daniell]: each mu_a in
    the product theorem is itself a normalized monotone Daniell
    integral on K(X_a), Federer 2.6.6, p. 120. *)
Theorem infinite_product_marginal_daniell (R : realType) (I : choiceType) (Y : I -> topologicalType)
  (A : forall i, (Y i -> R) -> R)
  (hh : forall i, hausdorff_space (Y i)) (hc : forall i, compact (@setT (Y i)))
  (hA : forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i))
  (hA1 : forall i, A i (fun _=>1) = 1) F :
  is_monotone_daniell_integral (@compactly_supported_continuous_functions R (finite_coordinate_space Y F))
    (finite_coordinate_marginal (@finite_coordinate_product R I Y A hh hc hA hA1) F) /\
  finite_coordinate_marginal (@finite_coordinate_product R I Y A hh hc hA hA1) F (fun _=>1) = 1.
Proof.
have [x0 _] := normalized_daniell_product_nonempty hA hA1.
have hs := @finite_coordinate_product_specification R I Y A hh hc hA hA1.
exact: (@finite_coordinate_marginal_is_daniell R I Y x0 _ F hh (compact_factor_product_compact hc)
  (finite_coordinate_product_consistency hs)).
Qed.
