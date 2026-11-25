(** Federer (1969), 1.7.5, pp. 32-33: the general wedge bound with binomial
    constant, in finite orthonormal coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerExterior InnerExteriorPositivity
  InnerExteriorBasis ExteriorNorm ExteriorBasisWedgeNorm OrthonormalFamilies
  OrthonormalParseval OrthonormalBilinearCoordinates GramSchmidt OrthonormalisationUP
  ExteriorWedgeCoordinateExpansion ExteriorIndexSupport ExteriorIndexSupportCard
  FiniteSparseSumBound LinearBasis ExteriorIndices Shuffles
  FiniteExteriorPowers ExteriorGrading ExteriorHomogeneousProducts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [orthonormal_wedge_squared_bound]: Federer
    1.7.5, pp. 32-33, the displayed chain of estimates
    in orthonormal coordinates, before taking square roots. *)
Theorem orthonormal_wedge_squared_bound (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) (ho : orthonormal_family B e)
    p q (c : Lambda n p -> R) (d : Lambda n q -> R) :
  exterior_norm h2 hB
    (exterior_product (\sum_lambda c lambda *: e_lambda e (val lambda))
      (\sum_mu d mu *: e_lambda e (val mu)))^+2 <=
    ('C(p+q,p))%:R * (\sum_lambda (c lambda)^+2) * (\sum_mu (d mu)^+2).
Proof.
rewrite exterior_norm_square
  (@orthonormal_parseval R (exterior_power V (p+q))
    (@exterior_inner_form R h2 V B hB (p+q)) (@exterior_inner_productP R h2 V B hB (p+q))
    (Finite.clone (Lambda n (p+q)) _) (fun nu => e_lambda e (val nu))
    (@exterior_orthonormal_family R h2 V B hB n e ho (p+q))
    (@finite_e_lambda_basis R n V e he h2 (p+q))).
under eq_bigr do rewrite (exterior_wedge_coordinate_expansion h2 hB ho).
have hh := @finite_sparse_sum_squared_bound R
  (Finite.clone (Lambda n p * Lambda n q)%type _) (Finite.clone (Lambda n (p+q)) _)
  (fun lm nu => exterior_index_support lm.1 lm.2 nu)
  (fun lm => (c lm.1*d lm.2)*(-1:R)^+(inversions (map val (val lm.1++val lm.2))))
  'C(p+q,p) (@exterior_index_support_card_bound n p q)
  (fun lm nu rho => @exterior_index_support_unique n p q lm.1 lm.2 nu rho).
apply: le_trans hh _.
have hs : (\sum_(lm : (Lambda n p * Lambda n q)%type)
    ((c lm.1*d lm.2)*(-1:R)^+(inversions (map val (val lm.1++val lm.2))))^+2) =
    (\sum_lambda (c lambda)^+2) * (\sum_mu (d mu)^+2).
  rewrite big_distrlr pair_big /=; apply: eq_bigr => [[lambda mu]] _ /=.
  by rewrite !exprMn sqrr_sign mulr1.
by rewrite hs mulrA.
Qed.

(** Source for [finite_wedge_squared_bound]: Federer 1.7.5,
    pp. 32-33, the binomial squared-norm bound for arbitrary
    multivectors in a finite-dimensional inner-product space. *)
Theorem finite_wedge_squared_bound (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e)
    p q (x : exterior_power V p) (y : exterior_power V q) :
  exterior_norm h2 hB (exterior_product x y)^+2 <=
    ('C(p+q,p))%:R * (exterior_norm h2 hB x)^+2 * (exterior_norm h2 hB y)^+2.
Proof.
have [d [hd hdo]] := @orthonormal_basis_exists R V B hB n e he.
have ho := orthonormalisation_orthonormal hdo.
have hb := @finite_e_lambda_basis R n V d hd h2 p.
have hc := @finite_e_lambda_basis R n V d hd h2 q.
rewrite (@orthonormal_basis_vector_expansion R (exterior_power V p)
  (Finite.clone (Lambda n p) _) (fun lambda => e_lambda d (val lambda)) hb x)
  (@orthonormal_basis_vector_expansion R (exterior_power V q)
  (Finite.clone (Lambda n q) _) (fun mu => e_lambda d (val mu)) hc y).
rewrite !(@exterior_basis_expansion_norm_square R h2 V B hB n d ho).
exact: (@orthonormal_wedge_squared_bound R h2 V B hB n d hd ho p q).
Qed.
