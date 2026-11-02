(** Federer (1969), 1.7.5, p. 32: the simple-factor wedge norm inequality in
    an arbitrary inner-product space. The finite support argument removes
    all ambient dimension restrictions. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductRestriction OrthogonalMaps
  ExteriorNorm ExteriorNormNaturality FiniteSimpleWedgeNorm ExteriorPairReduction
  ModuleQuotient SubspaceCarrier FiniteSpanSpace
  ExteriorGrading ExteriorMaps FiniteExteriorPowers ExteriorHomogeneousProducts
  AssociatedSubspace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [simple_right_wedge_norm_bound]: Federer
    1.7.5, p. 32, a simple right factor gives the constant-one
    wedge bound, without assuming finite dimension. *)
Theorem simple_right_wedge_norm_bound (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    p q (x : exterior_power V p) (y : exterior_power V q) :
  simple y -> exterior_norm h2 hB (exterior_product x y) <=
    exterior_norm h2 hB x * exterior_norm h2 hB y.
Proof.
move=> hy.
have [n [e [he [a [b [ha hb]]]]]] := exterior_pair_finite_reduction x y.
pose S := finite_span_subspace e.
pose C := @restricted_inner_product R V B S.
have hC := @restricted_inner_productP R V B hB S.
have hi : is_orthogonal_map C B (subspace_inclusion S) by [].
have hr : exterior_power_map (subspace_retraction S) q y = b.
  rewrite -hb; exact: (@exterior_power_mapK R (finite_span_vect he) V
    (subspace_inclusion S) (subspace_retraction S) (@subspace_retractionK R V S) q b).
have hsb : simple b.
  rewrite -hr; exact: exterior_power_map_simple hy.
have hh := @finite_simple_right_wedge_norm_bound R h2 (finite_span_vect he)
  C hC n (finite_span_basis e) (finite_span_basisP he) p q a b hsb.
rewrite -ha -hb -exterior_power_map_product.
by rewrite !(@exterior_norm_orthogonal_natural R h2 (finite_span_vect he) V C B hC hB
  (subspace_inclusion S) hi).
Qed.

(** Source for [simple_wedge_norm_bound]: Federer 1.7.5,
    p. 32, the stated estimate |xi wedge eta| <= |xi| |eta|
    whenever either factor is simple. *)
Theorem simple_wedge_norm_bound (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    p q (x : exterior_power V p) (y : exterior_power V q) :
  simple x \/ simple y -> exterior_norm h2 hB (exterior_product x y) <=
    exterior_norm h2 hB x * exterior_norm h2 hB y.
Proof.
move=> [hx|hy]; last exact: simple_right_wedge_norm_bound.
rewrite exterior_product_norm_swap mulrC; exact: simple_right_wedge_norm_bound.
Qed.
