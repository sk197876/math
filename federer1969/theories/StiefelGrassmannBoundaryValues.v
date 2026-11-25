(** Federer (1969), 3.2.28(2)–(5), pp. 265–267:
    boundary values of the actual volume formulas,
    including positive atomic degree-zero targets. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal topology.
From Federer Require Import EuclideanManifoldVolumes EuclideanStiefelVolumeRecurrence EuclideanStiefelEmptyFrameVolume
  EuclideanGrassmannGammaVolume GrassmannGammaVolumeScalar StiefelGammaProduct
  EulerGamma EulerGammaHalfParameters SphereGammaMass RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_first_frame_gamma_volume]: the
    base O(n,1) is the unit sphere in the
    volume induction of Federer 3.2.28(5), p. 267;
    its exact Gamma mass is 3.2.13, p. 251. *)
Theorem euclidean_first_frame_gamma_volume (R:realType) n (hPos:(0<n)%N):
  euclidean_stiefel_volume R n 1=
    (2*(euler_gamma_half R)^+n/euler_gamma (@positive_dimension_half R n hPos))%R%:E.
Proof.
rewrite (@euclidean_stiefel_volume_recurrence R n 0 hPos)
  euclidean_stiefel_empty_frame_volume expr0 mul1e mule1 subn0.
exact:hausdorff_unit_sphere_gamma_mass.
Qed.

(** Source for [euclidean_full_grassmann_volume]: G(n,n)
    has one point of H^0 mass one, the
    m=n boundary in Federer 3.2.28(4),(5), p. 267.
    The positive degree is retained. *)
Theorem euclidean_full_grassmann_volume (R:realType) n:
  (0<n)%N ->euclidean_grassmann_volume R n n= 1.
Proof.
move=>hPos.
have h:=@euclidean_grassmann_gamma_volume R n n (leqnn n) hPos.
have hPi:stiefel_gamma_product R (leqnn n)!=0%R.
  by rewrite gt_eqF //; exact:stiefel_gamma_product_positive.
by rewrite /grassmann_gamma_volume_scalar subrr mulr0 real_power_zero_exponent
  mul1r divff // in h.
Qed.

(** Source for [euclidean_full_oriented_grassmann_volume]:
    the two orientations of the full n-plane
    have H^0 mass two, the positive m=n
    boundary of Federer 3.2.28(2),(4), pp. 265,267. *)
Theorem euclidean_full_oriented_grassmann_volume (R:realType) n:
  (0<n)%N ->euclidean_oriented_grassmann_volume R n n=(2:R)%:E.
Proof.
move=>hPos; by rewrite (@euclidean_grassmann_volume_orientation R n n hPos (leqnn n))
  (@euclidean_full_grassmann_volume R n hPos) mule1.
Qed.
