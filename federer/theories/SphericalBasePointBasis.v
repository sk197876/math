(** Federer (1969), 3.2.47, p. 282: an actual
    unit c admits an orthonormal basis beginning with c.
    The choice is local to the existence proof and is not
    an additional hypothesis of the numbered assertions. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerProductUP InnerNormalization InnerNorm OrthonormalFamilies OrthogonalMaps
  LinearBasis FiniteBasisCriterion FiniteBasisComparison FiniteIndependence
  IndependentMap FiniteDimension EuclideanStiefelInnerSplitting UnitVectorOrthogonalMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [spherical_base_point_basis_exists]: the local
    orthonormal basis e_1,...,e_n with e_1=c
    chosen in 3.2.47, p. 282, exists for every
    actual unit c and every positive ambient dimension. *)
Theorem spherical_base_point_basis_exists (R:realType) n (c:R_n R n.+1):
  inner_norm (@euclidean_inner_productP R n.+1) c= 1 ->
  exists e:'I_n.+1->R_n R n.+1,is_basis e /\
    orthonormal_family (@euclidean_inner_product R n.+1) e /\e ord0=c.
Proof.
move=>hc.
have hCoordinate:inner_norm (@euclidean_inner_productP R n.+1)
    (@coordinate_basis R n.+1 ord0)= 1.
  exact (@orthonormal_norm1 R (R_n R n.+1) (@euclidean_inner_product R n.+1)
    (@euclidean_inner_productP R n.+1) (Finite.clone 'I_n.+1 _)
    (@coordinate_basis R n.+1) (@euclidean_coordinate_orthonormal_family R n.+1) ord0).
have [f [hf hFirst]]:=@unit_vector_orthogonal_map_exists R n.+1
  (@coordinate_basis R n.+1 ord0) c (ltn0Sn n) hCoordinate hc.
pose e:=fun i=>f (@coordinate_basis R n.+1 i).
have hIndependent:finite_independent e.
  apply:(@finite_independent_map R (Finite.clone 'I_n.+1 _) (R_n R n.+1)
    (R_n R n.+1) f (@coordinate_basis R n.+1)).
  - exact (@orthogonal_map_injective R (R_n R n.+1) (R_n R n.+1) _ _
      (@euclidean_inner_productP R n.+1) (@euclidean_inner_productP R n.+1) f hf).
  - exact:finite_basis_independent (@coordinate_basisP R n.+1).
have hBasis:is_basis e.
  apply:(@finite_independent_basis R (finite_basis_vect (@coordinate_basisP R n.+1)) n.+1 e).
  - by rewrite finite_basis_dimension card_ord.
  - exact hIndependent.
exists e; split; first exact hBasis.
split; last exact hFirst.
move=>i j; rewrite /e hf; exact:euclidean_coordinate_orthonormal_family.
Qed.
