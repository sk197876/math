(** Federer (1969), 3.2.28, pp. 263–267:
    principal smooth-manifold and closed Hausdorff-volume
    conclusions. The differential, fibre, coarea and
    general square-map area theorems are exposed separately. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Export EuclideanStiefelSmooth EuclideanOrientedGrassmannSmooth EuclideanGrassmannSquare
  EuclideanExteriorPartialJacobian EuclideanForgetfulPartialJacobian EuclideanExteriorCoareaVolume
  EuclideanForgetfulCoareaVolume SymmetricSquareManifoldArea EuclideanManifoldVolumes
  EuclideanStiefelGammaVolume EuclideanGrassmannGammaVolume StiefelGrassmannBoundaryValues.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps OrthogonalMaps
  EuclideanHomInnerCharts ExteriorGrading ExteriorNorm InnerExterior InnerExteriorPositivity AssociatedSubspace
  SymmetricGrading InnerSymmetric InnerSymmetricPositivity FiniteInnerSmoothSubmanifoldUP
  StiefelGammaVolumeScalar GrassmannGammaVolumeScalar.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_2_28]: the smooth Stiefel and
    oriented/unoriented Grassmann manifolds with their
    printed dimensions and both closed Gamma volume
    formulas, Federer 3.2.28(1),(2),(4),(5),
    pp. 263–267. The supporting public theorems
    retain all computed differentials and exact tangent
    Jacobians, actual SO and spherical fibres, both
    coarea identities, and the square-area identity on
    every antipodal manifold, including noncompact ones.
    Erratum p. 5, book p. 265 lines 3/12:
    delete the compactness phrase and use alpha in
    O(m,m-1); these are applied in the supporting proofs. *)
Theorem federer_3_2_28 (R:realType) n m (hmn:(m<=n)%N):
  (0<m)%N ->
  let E:=exterior_power (R_n R n) m in
  let B:=@exterior_inner_form R (euclidean_two_nonzero R) (R_n R n)
    (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m in
  let hB:=@exterior_inner_productP R (euclidean_two_nonzero R) (R_n R n)
    (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m in
  is_inner_smooth_submanifold (@euclidean_hom_inner_product R m n) (m*(2*n-m-1)%/2)%N
    [set g|is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R n) (hom_as_linear g)] /\
  is_inner_smooth_submanifold B (m*(n-m))%N
    [set x|simple x /\exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n) x= 1] /\
  is_inner_smooth_submanifold (@symmetric_inner_form R E B hB 2) (m*(n-m))%N
    (@euclidean_grassmann_square_set R n m) /\
  euclidean_stiefel_volume R n m=(stiefel_gamma_volume_scalar R hmn)%:E /\
  euclidean_grassmann_volume R n m=(grassmann_gamma_volume_scalar R hmn)%:E.
Proof.
move=>hm E B hB; split; first exact:euclidean_stiefel_smooth_submanifold.
split; first exact:euclidean_oriented_grassmann_smooth_submanifold hm hmn.
split; first exact:euclidean_grassmann_smooth_submanifold hm hmn.
split; first exact:euclidean_stiefel_gamma_volume.
exact:euclidean_grassmann_gamma_volume hmn hm.
Qed.
