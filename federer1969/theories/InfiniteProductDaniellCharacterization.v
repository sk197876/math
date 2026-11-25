(** Federer (1969), 2.6.6, p. 120: "We note that mu is uniquely
    characterized by the condition: p_a#(mu) = mu_a whenever a in A." Here
    p_a#(D)(g) = D(g o p_a) for g in K(X_a). The competitor D ranges over
    all Daniell integrals on K(X), with no monotonicity or normalisation
    hypothesis. Since X is compact, D is continuous for the norm nu of
    2.5.19, p. 113, and the uniqueness of the continuous extension of gamma
    from the dense union L applies. it has no infinite-product integral. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP DaniellIntegralUP MonotoneDaniellIntegralUP
  MonotoneDaniellIntegralSum ConsistentCylinderFunctionalUP FiniteCoordinateProjection
  FiniteCoordinatePullback FiniteCoordinateMarginal FiniteCoordinateProduct InfiniteDaniellProduct
  InfiniteProductMarginals InfiniteProductContinuousExtension NormalizedProductSpace
  CompactDaniellUniformContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Characterization.
Variables (R : realType) (I : choiceType) (Y : I -> topologicalType).
Variables (A : forall i, (Y i -> R) -> R).
Variables (hh : forall i, hausdorff_space (Y i)) (hc : forall i, compact (@setT (Y i))).
Variables (hA : forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (@A i))
  (hA1 : forall i, @A i (fun _=>1) = 1).
Local Notation X := (prod_topology Y).
Local Notation K := (@compactly_supported_continuous_functions R X).
Local Notation mu := (@infinite_daniell_product R I Y A hh hc hA hA1).
Local Notation C := (@finite_coordinate_product R I Y A hh hc hA hA1).

(** Source for [has_finite_product_marginals]: the condition
    p_a#(D) = mu_a whenever a in A of Federer 2.6.6, p. 120, for a
    functional D on functions on X; p_a#(D) is evaluated on K(X_a). *)
Definition has_finite_product_marginals (D : (X -> R) -> R) :=
  forall (F : {fset I}) (g : finite_coordinate_space Y F -> R),
    compactly_supported_continuous_functions g ->
    D (g \o finite_coordinate_projection (F:=F))=finite_coordinate_marginal C F g.

(** Source for [infinite_daniell_product_has_marginals]: the product
    integral mu satisfies p_a#(mu) = mu_a whenever a in A, Federer
    2.6.6, p. 120. *)
Lemma infinite_daniell_product_has_marginals : has_finite_product_marginals mu.
Proof. move=> F g hg; exact: infinite_product_finite_marginal. Qed.

(** Source for [infinite_daniell_product_daniell_unique]: direct
    formalisation of "mu is uniquely characterized by the condition
    p_a#(mu) = mu_a whenever a in A", Federer 2.6.6, p. 120, among
    all Daniell integrals on K(X). The competitor need not be monotone
    or normalised; equality is asserted on K(X), the domain of the
    Daniell integrals. *)
Theorem infinite_daniell_product_daniell_unique (D : (X -> R) -> R) :
  is_daniell_integral K D -> has_finite_product_marginals D -> forall f, K f -> D f=mu f.
Proof.
move=> hD hDm.
have [x0 _] := normalized_daniell_product_nonempty hA hA1.
have hX := compact_factor_product_compact hc.
apply: (@infinite_product_continuous_extension_unique R I Y A hh hc hA hA1 D).
- exact: compact_daniell_uniform_continuous hX hD.
- move=> F f hf.
  have [g [hg ->]] := (proj1 (@finite_coordinate_cylinder_image R I Y x0 F f hX)) hf.
  exact: hDm F g hg.
Qed.

(** Source for [infinite_daniell_product_daniell_characterization]:
    the characterization of Federer 2.6.6, p. 120, as an equivalence
    for an arbitrary Daniell integral D on K(X): D has the marginals
    mu_a if and only if D agrees with mu on K(X). *)
Theorem infinite_daniell_product_daniell_characterization (D : (X -> R) -> R) :
  is_daniell_integral K D -> (has_finite_product_marginals D <-> forall f, K f -> D f=mu f).
Proof.
move=> hD; split; first exact: infinite_daniell_product_daniell_unique.
move=> he F g hg.
have hX := compact_factor_product_compact hc.
rewrite (he _ (finite_coordinate_pullback_membership hX hg).1).
exact: infinite_daniell_product_has_marginals.
Qed.

(** Source for [finite_product_marginals_determine_daniell]: two
    Daniell integrals on K(X) with the same marginals mu_a for every
    finite a coincide on K(X), Federer 2.6.6, p. 120; neither is
    assumed monotone or normalised. *)
Theorem finite_product_marginals_determine_daniell (B D : (X -> R) -> R) :
  is_daniell_integral K B -> is_daniell_integral K D ->
  has_finite_product_marginals B -> has_finite_product_marginals D -> forall f, K f -> B f=D f.
Proof.
move=> hB hD hBm hDm f hf.
by rewrite (infinite_daniell_product_daniell_unique hB hBm hf) (infinite_daniell_product_daniell_unique hD hDm hf).
Qed.
End Characterization.
