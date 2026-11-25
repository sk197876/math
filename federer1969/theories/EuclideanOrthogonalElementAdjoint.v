(** Federer (1969), 3.3.4, pp. 289–291:
    the actual group inverse in the
    original frame is the actual orthogonal
    adjoint of 1.7.4, p. 30. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanRectangularAdjoint EuclideanOrthogonalAdjointInverse
  EuclideanOrthogonalInvariantMeasures OrthogonalGroupHaarMeasure
  IsotropyGroupTopology LinearGroupTopology LinearGroupSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [euclidean_orthogonal_element_inverse_adjoint]:
    actual inverse-frame coordinates can be
    calculated with the sealed adjoint,
    supporting Federer 3.3.4, pp. 289–291,
    by 1.7.4, p. 30. Uniqueness
    follows from the actual group left
    inverse and adjoint right inverse. *)
Theorem euclidean_orthogonal_element_inverse_adjoint (R:realType) n
    (mulS:euclidean_orthogonal_group R n->euclidean_orthogonal_group R n->euclidean_orthogonal_group R n)
    (invS:euclidean_orthogonal_group R n->euclidean_orthogonal_group R n)
    (eS:euclidean_orthogonal_group R n)
    (hS:is_subgroup_restriction
      (linear_group_mul (@euclidean_inner_productP R n) (@coordinate_basisP R n))
      (linear_group_inv (@euclidean_inner_productP R n) (@coordinate_basisP R n))
      (linear_group_unit (@euclidean_inner_productP R n) (@coordinate_basisP R n))
      (euclidean_orthogonal_group R n) mulS invS eS)
    (g:euclidean_orthogonal_group R n):
  orthogonal_element_map (invS g)=euclidean_rectangular_adjoint (orthogonal_element_map g).
Proof.
have hLeft:=(orthogonal_element_inv hS g).1.
have hRight:=euclidean_orthogonal_adjoint_cancel_reverse (orthogonal_element_orthogonal g).
apply:hom_ext=>x.
have hPoint:=hLeft (euclidean_rectangular_adjoint (orthogonal_element_map g) x).
by rewrite hRight in hPoint.
Qed.
