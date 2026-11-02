(** Federer (1969), 3.2.28(5), p. 267:
    the printed closed Euler Gamma formula for the
    actual Hausdorff volume of O(n,m). *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal topology.
From Federer Require Import EuclideanManifoldVolumes EuclideanStiefelVolumeRecurrence EuclideanStiefelEmptyFrameVolume
  StiefelGammaVolumeScalar SphereGammaMass EulerGammaHalfParameters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_stiefel_gamma_volume]: the first
    displayed closed volume formula of Federer
    3.2.28(5), p. 267. The actual coarea
    recurrence, actual sphere Gamma mass and proved
    scalar recurrence identify the Hausdorff volume.
    Its empty-frame extension has mass one. *)
Theorem euclidean_stiefel_gamma_volume (R:realType) n m (hmn:(m<=n)%N):
  euclidean_stiefel_volume R n m=(stiefel_gamma_volume_scalar R hmn)%:E.
Proof.
elim:m hmn=>[hmn|k IH hkn].
- by rewrite euclidean_stiefel_empty_frame_volume stiefel_gamma_volume_scalar_zero.
- have hk:(k<=n)%N:=leq_trans (leqnSn k) hkn.
  have hPos:(0<n-k)%N by rewrite subn_gt0.
  rewrite (@euclidean_stiefel_volume_recurrence R n k hkn)
    (@hausdorff_unit_sphere_gamma_mass R (n-k) hPos) (IH hk) -!EFinM
    -(@stiefel_gamma_volume_scalar_successor R n k hkn hk hPos).
  reflexivity.
Qed.
