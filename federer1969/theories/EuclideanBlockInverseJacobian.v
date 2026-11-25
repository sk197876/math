(** Federer (1969), 3.2.10, p. 248: the
    displayed Jacobian identity in Cartesian block coordinates.
    This adapter changes only the equal complementary degree;
    its substance is the independently proved contraction identity. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanLinearMaps EuclideanLinearJacobian EuclideanBlockLinearMaps
  EuclideanCoordinateVolumes EuclideanBlockVolumes EuclideanFrameJacobian
  CoordinateInverseJacobian CoordinateProjection InitialIndices TopComplements
  ExteriorGrading ExteriorMaps ExteriorHomogeneousProducts ExteriorNorm
  ExteriorNormNaturality FiniteExteriorPowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [euclidean_block_inverse_jacobian]: the
    equality J_n D=J_k(M restricted to the last block) J_(n+k) T
    in Federer 3.2.10, p. 248, for the actual inverse
    diagram. No orthogonal kernel basis or extra Jacobian
    hypothesis is assumed; both zero-dimensional blocks are covered. *)
Theorem euclidean_block_inverse_jacobian (R:realType) n k
    (T M:Hom (R_n R (n+k)) (R_n R (n+k)))
    (D:Hom (R_n R (n+k)) (R_n R n)):
  cancel T M ->(forall x,D (M x)=@euclidean_first_block R n k x) ->
  euclidean_linear_jacobian n D=
    euclidean_linear_jacobian k (hom_comp M (@euclidean_last_injection_map R n k))*
    euclidean_linear_jacobian (n+k) T.
Proof.
move=>hTM hD.
have hDCoord x:D (M x)=coordinate_projection (Lambda_initial (leq_addr k n)) x.
  by rewrite hD euclidean_first_block_coordinate_projection.
have hOld:=@coordinate_inverse_jacobian R (n+k) n (leq_addr k n) T M D hTM hDCoord.
have hFrame:=euclidean_frame_jacobian M (hom_as_linear (@euclidean_last_injection_map R n k)).
rewrite hom_of_asK in hFrame.
have hJ:euclidean_linear_jacobian ((n+k)-n)
    (hom_comp M (hom_of_linear (@coordinate_injection R (n+k) ((n+k)-n)
      (top_complement (Lambda_initial (leq_addr k n))))))=
    euclidean_linear_jacobian k (hom_comp M (@euclidean_last_injection_map R n k)).
  rewrite euclidean_frame_jacobian coordinate_injection_top_product hFrame.
  rewrite -(@exterior_norm_reindex R (euclidean_two_nonzero R) (R_n R (n+k))
    (@euclidean_inner_product R (n+k)) (@euclidean_inner_productP R (n+k))
    ((n+k)-n) k (addKn n k)
    (exterior_power_map (hom_as_linear M) ((n+k)-n)
      (e_lambda (@coordinate_basis R (n+k))
        (val (top_complement (Lambda_initial (leq_addr k n))))))).
  by rewrite exterior_map_reindex_degree euclidean_last_block_top_volume.
by rewrite hJ in hOld.
Qed.
