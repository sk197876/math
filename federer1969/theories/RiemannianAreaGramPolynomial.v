(** Federer (1969), 3.2.46, p. 282: area Jacobians
    computed in the actual target inner product. This
    supporting polynomial formula expands 1.7.5–1.7.6,
    pp. 31–34, through the public exterior-product and
    norm laws. It does not redefine the Jacobian. *)
From mathcomp Require Import all_boot all_order all_algebra reals fingroup perm.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanLinearMaps InnerProductUP InnerNorm InnerExterior InnerExteriorPositivity InnerExteriorProducts
  ExteriorGrading ExteriorMaps ExteriorNorm FiniteExteriorPowers ExteriorFrameUnitNorm ExteriorOperatorEstimate
  TopExteriorNorm InversionCount RiemannianLinearJacobian.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [riemannian_area_gram_polynomial]: the square
    of the actual Euclidean-source area Jacobian is the Gram
    determinant in the Riemannian target inner product,
    supporting 3.2.46, p. 282, by the permutation formula
    of 1.7.5, p. 32. Singular maps, m>n and the
    zero-dimensional empty product are all retained. *)
Lemma riemannian_area_gram_polynomial (R : realType) m n C
    (hC : @is_inner_product R (R_n R n) C)
    (D : Hom (R_n R m) (R_n R n)) :
  riemannian_linear_jacobian (@euclidean_inner_productP R m) hC m D ^+ 2 =
    \sum_(sigma : 'S_m) FedererPermutation.index R sigma *
      \prod_(i < m) C (D (@coordinate_basis R m (sigma i))) (D (@coordinate_basis R m i)).
Proof.
pose h2 := euclidean_two_nonzero R.
pose w := e_lambda (@coordinate_basis R m) (ord_tuple m).
have hw : exterior_norm h2 (@euclidean_inner_productP R m) w = 1.
  exact: euclidean_top_product_unit_norm.
rewrite /riemannian_linear_jacobian
  (@top_exterior_operator_unit_value R h2 (R_n R m) (R_n R n)
    (@euclidean_inner_product R m) C (@euclidean_inner_productP R m) hC
    m (@coordinate_basis R m) (@coordinate_basisP R m) (hom_as_linear D) w hw).
rewrite /w exterior_map_indexed_product exterior_norm_square
  exterior_inner_product_permutations.
apply: eq_bigr=> sigma _; congr (_*_).
by rewrite foldrE big_map enumT.
Qed.

(** Source for [riemannian_area_jacobian_gram_root]: the
    actual area Jacobian is the nonnegative square root
    of the preceding finite Gram polynomial, supporting
    its measurability in 3.2.46, p. 282. No
    positive-rank hypothesis or chosen frame is needed. *)
Lemma riemannian_area_jacobian_gram_root (R : realType) m n C
    (hC : @is_inner_product R (R_n R n) C)
    (D : Hom (R_n R m) (R_n R n)) :
  riemannian_linear_jacobian (@euclidean_inner_productP R m) hC m D =
    Num.sqrt (\sum_(sigma : 'S_m) FedererPermutation.index R sigma *
      \prod_(i < m) C (D (@coordinate_basis R m (sigma i))) (D (@coordinate_basis R m i))).
Proof.
rewrite -(@riemannian_area_gram_polynomial R m n C hC D) sqrtr_sqr.
by rewrite (ger0_norm (@riemannian_linear_jacobian_nonnegative R m n (@euclidean_inner_product R m) C
  (@euclidean_inner_productP R m) hC m D)).
Qed.
