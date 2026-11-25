(** Federer (1969), 2.6.6, p. 120: the unique continuous linear extension of
    gamma, including uniqueness among all continuous extensions, not only
    normalized Daniell integrals. Source context:
    CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP MonotoneDaniellIntegralUP MonotoneDaniellIntegralSum
  InfiniteDaniellProductUP InfiniteDaniellProduct FiniteCoordinateProduct ProductCylinderLattice
  ConsistentCylinderFunctionalUP NormalizedProductSpace ProductCylinderDensity
  NormalizedDaniellUniformLipschitz DenseScalarContinuousUniqueness
  FunctionSeminormDistance UniformFunctionNorm FunctionLatticeSeminormUP DaniellSpaceCompactness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Extension.
Variables (R : realType) (I : choiceType) (Y : I -> topologicalType).
Variables (A : forall i, (Y i -> R) -> R).
Variables (hh : forall i, hausdorff_space (Y i)) (hc : forall i, compact (@setT (Y i))).
Variables (hA : forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (@A i))
  (hA1 : forall i, @A i (fun _=>1) = 1).
Local Notation X := (prod_topology Y).
Local Notation K := (@compactly_supported_continuous_functions R X).
Local Notation L := (@continuous_product_cylinders R I Y).
Local Notation d := (function_seminorm_distance (@compact_support_uniform_norm R X)).
Local Notation B := (@infinite_daniell_product R I Y A hh hc hA hA1).
Local Notation C := (@finite_coordinate_product R I Y A hh hc hA hA1).

(** Source for [infinite_product_continuous_linear]: the
    continuous linear extension in Federer 2.6.6, p. 120,
    with continuity for the actual uniform norm of K(X). *)
Theorem infinite_product_continuous_linear :
  is_linear_functional_on_functions K B /\ is_scalar_continuous_on_set K d B.
Proof.
have hb := @infinite_daniell_product_specification R I Y A hh hc hA hA1.
split.
- exact: daniell_compact_support_linear (monotone_daniell_integral_is_daniell hb.1).
- apply: scalar_lipschitz_implies_continuous.
  exact: normalized_daniell_uniform_lipschitz (compact_factor_product_compact hc) hb.1 hb.2.1.
Qed.

(** Source for [infinite_product_continuous_extension_unique]:
    uniqueness of the continuous extension stated in Federer
    2.6.6, p. 120. A competing functional need only be
    continuous and agree on every finite cylinder; linearity
    then follows from its equality with the product. *)
Theorem infinite_product_continuous_extension_unique (D : (X -> R) -> R) :
  is_scalar_continuous_on_set K d D ->
  (forall F f, continuous_coordinate_functions F f -> D f=C F f) ->
  forall f, K f -> D f=B f.
Proof.
move=> hD hDC.
have [x0 _] := normalized_daniell_product_nonempty hA hA1.
have hb := @infinite_daniell_product_specification R I Y A hh hc hA hA1.
apply: (@dense_scalar_continuous_unique R (X -> R) K L d D B).
- by move=> f hf; exact: hf.1.
- exact: compact_product_cylinders_uniformly_dense x0 (compact_factor_product_compact hc).
- exact: hD.
- exact: infinite_product_continuous_linear.2.
- move=> f [hf [F hF]]; by rewrite (hDC F f (conj hf hF)) (hb.2.2 F f (conj hf hF)).
Qed.
End Extension.
