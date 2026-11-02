(** Federer (1969), 3.2.33, p. 270: the actual
    mu-dimensional exterior Jacobian of Df is at least one. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanLinearMaps
  CoordinateProjection OrthonormalFamilies FiniteExteriorPowers ExteriorGrading ExteriorMaps
  ExteriorNorm ExteriorHadamardEquality ExteriorOperatorEstimate EuclideanExteriorComposition
  EuclideanLinearJacobian ScalarCylinderMapUP ScalarCylinderBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_cylinder_jacobian_lower_bound]: the
    inequality J_mu f>= 1 in Federer 3.2.33, p. 270.
    The preserved first mu standard directions give an actual
    unit exterior word whose image also has norm one.
    The operator-norm bound proves the inequality. The empty
    word retains mu= 0 with its unit norm. *)
Theorem scalar_cylinder_jacobian_lower_bound (R:realType) mu k c
    (L:Hom (R_n R ((mu+1)+k)) (R_n R (mu+1))):
  is_scalar_cylinder_map (fun t=>c*t) L ->1<=euclidean_linear_jacobian mu L.
Proof.
move=>hL.
pose idx i:'I_((mu+1)+k):=lshift k (lshift 1 i).
pose e i:=@coordinate_basis R ((mu+1)+k) (idx i).
have hInj:injective idx.
  move=>i j h; apply:val_inj; exact:(congr1 (fun a:'I_((mu+1)+k)=>(a:nat)) h).
have hSource:orthonormal_family (@euclidean_inner_product R ((mu+1)+k)) e.
  by move=>i j; rewrite /e euclidean_inner_basis /coordinate_basis ffunE (inj_eq hInj) eq_sym.
have hTarget:orthonormal_family (@euclidean_inner_product R (mu+1)) (fun i=>L (e i)).
  move=>i j; rewrite /e /idx !(scalar_cylinder_first_basis_image hL)
    euclidean_inner_basis /coordinate_basis ffunE.
  have hInjTarget:injective (@lshift mu 1).
    move=>a b h; apply:val_inj; exact:(congr1 (fun a:'I_(mu+1)=>(a:nat)) h).
  by rewrite (inj_eq hInjTarget) eq_sym.
pose w:=e_lambda e (ord_tuple mu).
have hNS:exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R ((mu+1)+k)) w= 1.
  exact:(orthonormal_product_unit_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R ((mu+1)+k)) hSource).
have hNT:exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R (mu+1))
    (exterior_power_map (hom_as_linear L) mu w)= 1.
  rewrite /w exterior_map_indexed_product.
  exact:(orthonormal_product_unit_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R (mu+1)) hTarget).
have hBound:=euclidean_exterior_jacobian_vector_bound L w.
by rewrite hNS hNT mulr1 in hBound.
Qed.
