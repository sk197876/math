(** Federer (1969), 1.10.5, p. 48: supporting auxiliary Euclidean structure
    for finite-dimensional norm comparisons and compactness. The
    construction is only a witness: the given norm is not replaced by a
    coordinate norm. The inner-product laws come from 1.7.1 and 1.7.9. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP FreeVector LinearBasis FiniteCoordinates EuclideanInnerProduct
  InnerProductUP InnerProductPullback OrthonormalFamilies CoordinateProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_basis_inner_product_witness]: Federer 1.10.5,
    p. 48, supporting finite-dimensional reduction. Any specified finite
    basis can be made orthonormal for some inner product; this supplies
    a witness for compactness arguments without changing the original norm. *)
Theorem finite_basis_inner_product_witness (R : realFieldType) (V : lmodType R)
    n (e : 'I_n -> V) (he : is_basis e) :
  exists B : V -> V -> R, is_inner_product B /\ orthonormal_family B e.
Proof.
pose F := linear_comp (GRing.Linear.clone _ _ _ _ (@coordinate_from_free R n) _) (basis_coordinates he).
have hin : injective F.
  move=> x y hxy; apply: (can_inj (basis_coordinatesK he)).
  apply: (can_inj (@coordinate_from_freeK R n)); exact hxy.
pose B := fun x y => euclidean_inner_product (F x) (F y).
exists B; split.
- exact (@inner_product_linear_pullback R V (coordinate_space R n)
    (@euclidean_inner_product R n) (@euclidean_inner_productP R n) F hin).
- have hF i : F (e i) = @coordinate_basis R n i.
    by rewrite /F /= basis_coordinatesE coordinate_from_free_delta.
  move=> i j; rewrite /B !hF euclidean_inner_basis.
  by rewrite /coordinate_basis ffunE eq_sym.
Qed.
