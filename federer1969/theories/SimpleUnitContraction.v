(** Federer (1969), 1.8.1, p. 39: supporting contraction estimate for the
    sharp comass product bound with a simple factor. Restrict to the
    associated space of the unit simple vector and use the duality of 1.6.3,
    pp. 24-25, and its isometry in 1.7.8, p. 34. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP InnerProductRestriction OrthogonalMaps
  ExteriorNorm ExteriorNormNaturality ExteriorMaps ExteriorGrading FiniteExteriorPowers
  ExteriorCovectorInner AlternatingCoordinates AlternatingDual LinearBasis
  AssociatedSubspace SubspaceCarrier SimpleCovectors SimpleUnitAssociatedLift
  CovectorProductNaturality CovectorProjectionNorm DualityBoundary DualityMaps
  UpperDualityNorm LeftInterior InteriorNaturality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [simple_covector_pullback]: Federer 1.8.1,
    p. 39, supporting transport of the simple factor to an associated
    subspace. Pullback preserves the product of its one-form factors,
    by the naturality used in 1.6.4, p. 25. *)
Lemma simple_covector_pullback (K : fieldType) (h2 : (1+1 : K) != 0)
    (U V : lmodType K) (f : {linear U -> V}) p (phi : A_m V K^o p) :
  simple_covector h2 phi -> simple_covector h2 (A_m_dual f phi).
Proof.
move=> [a ->]; rewrite one_forms_wedge_natural; by exists (fun i => A_m_dual f (a i)).
Qed.

(** Source for [simple_unit_contraction]: Federer 1.8.1,
    p. 39, supporting sharp bound: contracting a simple unit
    m-vector by a simple p-form gives a simple (m-p)-vector
    of norm at most the Euclidean norm of the p-form. Positive
    output degree is required by the literal simplicity convention. *)
Theorem simple_unit_contraction (R : realType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) p m (hpm : (p <= m)%N)
    (x : exterior_power V m) (phi : A_m V R^o p) :
  (p < m)%N -> simple x -> exterior_norm h2 hB x = 1 -> simple_covector h2 phi ->
  simple (left_interior h2 hpm x phi) /\
  exterior_norm h2 hB (left_interior h2 hpm x phi) <= exterior_covector_norm h2 hB he phi.
Proof.
move=> hlt hs hx hp.
have [b [hb [hE hiE]]] := @simple_unit_associated_lift R h2 V B hB m x hs hx.
pose U := subspace_space (FedererSimple.T x).
pose C := @restricted_inner_product R V B (FedererSimple.T x).
pose hC := restricted_inner_productP hB (FedererSimple.T x).
pose i := GRing.Linear.clone _ _ _ _ (@subspace_val R V (FedererSimple.T x)) _.
have hi : is_orthogonal_map C B i by [].
pose E := e_lambda b (ord_tuple m).
pose psi := A_m_dual i phi.
have hpsi : simple_covector h2 psi := simple_covector_pullback i hp.
have hz : simple (D_upper h2 E hpm psi) :=
  @D_upper_preserves_simple R h2 U m b hb E p hpm psi hlt hpsi.
have hn := @upper_duality_norm R h2 U C hC m b hb E hE p hpm psi.
have heq : exterior_power_map i (m-p) (D_upper h2 E hpm psi) = left_interior h2 hpm x phi.
  by rewrite /D_upper /psi left_interior_natural /E hiE.
split.
- rewrite -heq; exact: exterior_power_map_simple hz.
rewrite -heq (@exterior_norm_orthogonal_natural R h2 U V C B hC hB i hi) hn.
exact: (@orthogonal_covector_pullback_bound R h2 U V C B hC hB m n b e hb he i hi p phi).
Qed.
