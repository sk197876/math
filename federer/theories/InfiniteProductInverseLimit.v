(** Federer (1969), 2.6.6, pp. 120–121: "the passage from finite to infinite
    products depends only on the representation of X as inverse limit of the
    spaces X_a, and on the consistency conditions p^b_a#(mu_b) = mu_a." This
    file verifies the observation: the finite products mu_a form a
    consistent family over the inverse system of the spaces X_a, and the
    infinite product mu equals the inverse-limit integral of that family on
    K(X). *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP MonotoneDaniellIntegralUP FiniteCoordinateProjection
  FiniteCoordinateMarginal FiniteCoordinateProductUP FiniteCoordinateProduct InfiniteDaniellProductUP
  InfiniteDaniellProduct InfiniteProductMarginals CompactInverseSystemUP CompactInverseLimitUP
  InverseDaniellFamilyUP InverseDaniellIntegral InverseDaniellExtensionUniqueness
  FiniteCoordinateRestriction FiniteCoordinateInverseLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ProductInverseLimit.
Variables (R : realType) (I : choiceType) (Y : I -> topologicalType).
Variables (A : forall i, (Y i -> R) -> R).
Variables (hh : forall i, hausdorff_space (Y i)) (hc : forall i, compact (@setT (Y i))).
Variables (hA : forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (@A i))
  (hA1 : forall i, @A i (fun _=>1) = 1).
Variable x0 : prod_topology Y.
Local Notation X := (prod_topology Y).
Local Notation C := (@finite_coordinate_product R I Y A hh hc hA hA1).
Local Notation mu := (@infinite_daniell_product R I Y A hh hc hA hA1).

(** Source for [finite_product_inverse_daniell_family]: the finite
    products mu_a are normalised monotone Daniell integrals satisfying
    the consistency conditions p^b_a#(mu_b) = mu_a, Federer 2.6.6,
    p. 120, for the inverse system of the spaces X_a. *)
Theorem finite_product_inverse_daniell_family :
  is_consistent_inverse_daniell_family (@finite_coordinate_subset I) (@finite_coordinate_bonding I Y x0)
    (fun F=>finite_coordinate_marginal C F).
Proof.
split.
- move=> F; exact: (@infinite_product_marginal_daniell R I Y A hh hc hA hA1 F).1.
- move=> F; exact: (@infinite_product_marginal_daniell R I Y A hh hc hA hA1 F).2.
- move=> F G hFG f hf.
  have -> : f \o @finite_coordinate_bonding I Y x0 F G=f \o finite_coordinate_restriction hFG.
    by apply: funext=> u; rewrite /= (finite_coordinate_bonding_restriction x0 hFG u).
  have hs := @finite_coordinate_product_specification R I Y A hh hc hA hA1.
  have [h1 h2] := @finite_coordinate_marginal_restriction R I Y A hh hc hA hA1 C hs F G hFG f hf.
  by rewrite h1 h2.
Qed.

(** Source for [infinite_daniell_product_inverse_limit_integral]: the
    infinite product mu has the marginals mu_a on the inverse limit X,
    Federer 2.6.6, pp. 120–121. *)
Theorem infinite_daniell_product_inverse_limit_integral :
  is_inverse_limit_daniell_integral (fun F=>finite_coordinate_projection (F:=F))
    (fun F=>finite_coordinate_marginal C F) mu.
Proof.
have hs := @infinite_daniell_product_specification R I Y A hh hc hA hA1.
split; first exact: hs.1.
split; first exact: hs.2.1.
move=> F g hg; exact: infinite_product_finite_marginal.
Qed.

(** Source for [infinite_daniell_product_inverse_limit_value]: the
    infinite product of Federer 2.6.6, p. 120, is the inverse-limit
    integral of the finite products mu_a, as observed on pp. 120–121,
    on K(X). *)
Theorem infinite_daniell_product_inverse_limit_value (f : X -> R) :
  compactly_supported_continuous_functions f ->
  mu f=@inverse_limit_daniell_integral R _ (@finite_coordinate_subset I) _ (@finite_coordinate_bonding I Y x0)
    X (fun F=>finite_coordinate_projection (F:=F)) (fun F=>finite_coordinate_marginal C F)
    (@finite_coordinate_inverse_system I Y x0 hh hc) (@finite_coordinate_inverse_limit I Y x0 hh hc)
    finite_product_inverse_daniell_family f.
Proof.
move=> hf.
exact: (inverse_limit_daniell_integral_unique (@finite_coordinate_inverse_system I Y x0 hh hc)
  (@finite_coordinate_inverse_limit I Y x0 hh hc) finite_product_inverse_daniell_family
  infinite_daniell_product_inverse_limit_integral (inverse_limit_daniell_integral_specification _ _ _) hf).
Qed.
End ProductInverseLimit.
