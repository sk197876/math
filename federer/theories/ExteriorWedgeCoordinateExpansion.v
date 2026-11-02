(** Federer (1969), 1.7.5, pp. 32-33: coordinate expansion of xi wedge eta,
    grouped by the sets S(nu). *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerExterior InnerExteriorPositivity
  OrthonormalFamilies BilinearDoubleExpansion ExteriorBasisWedgeCoordinates
  ExteriorIndexSupport ExteriorIndices Shuffles ExteriorGrading
  ExteriorHomogeneousProducts FiniteExteriorPowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_wedge_coordinate_expansion]: Federer
    1.7.5, pp. 32-33, the coefficient of e_nu is the
    signed sum of xi_lambda eta_mu over pairs in S(nu). *)
Theorem exterior_wedge_coordinate_expansion (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : orthonormal_family B e)
    p q (c : Lambda n p -> R) (d : Lambda n q -> R) (nu : Lambda n (p+q)) :
  exterior_inner_form h2 hB
    (exterior_product (\sum_lambda c lambda *: e_lambda e (val lambda))
      (\sum_mu d mu *: e_lambda e (val mu))) (e_lambda e (val nu)) =
  \sum_(lm : (Lambda n p * Lambda n q)%type | exterior_index_support lm.1 lm.2 nu)
    (c lm.1 * d lm.2) * (-1 : R)^+(inversions (map val (val lm.1 ++ val lm.2))).
Proof.
rewrite -(inner_coordinateE (@exterior_inner_productP R h2 V B hB (p+q)))
  (bilinear_double_expansion (@exterior_product_bilinear R V p q)) linear_sum.
under eq_bigr do rewrite linear_sum.
rewrite pair_big [RHS]big_mkcond.
apply: eq_bigr => [[lambda mu]] _.
rewrite linearZ inner_coordinateE (exterior_basis_wedge_coordinate h2 hB he).
change ((c lambda * d mu) *
  (if exterior_index_support lambda mu nu
   then (-1 : R)^+(inversions (map val (val lambda ++ val mu))) else 0) =
  if exterior_index_support lambda mu nu then (c lambda * d mu) *
    (-1 : R)^+(inversions (map val (val lambda ++ val mu))) else 0).
by case: (exterior_index_support lambda mu nu); rewrite ?mulr0.
Qed.
