(** Federer (1969), 3.2.28(5), p. 267:
    the printed Euler Gamma formula for the actual
    unoriented Grassmann Hausdorff volume. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal topology lra ring.
From Federer Require Import EuclideanManifoldVolumes EuclideanStiefelGammaVolume
  StiefelGammaVolumeScalar GrassmannGammaVolumeScalar.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_grassmann_gamma_volume]: the
    second displayed closed volume formula in Federer
    3.2.28(5), p. 267. Actual coarea,
    actual two-to-one area and the positive finite
    Stiefel Gamma formula prove it; neither actual
    Grassmann volume nor positivity of an unspecified
    normalizing measure is assumed. *)
Theorem euclidean_grassmann_gamma_volume (R:realType) n m:
  forall hmn:(m<=n)%N,(0<m)%N ->
  euclidean_grassmann_volume R n m=(grassmann_gamma_volume_scalar R hmn)%:E.
Proof.
Local Open Scope ring_scope.
move=>hmn hm.
pose a:=stiefel_gamma_volume_scalar R hmn.
pose b:=stiefel_gamma_volume_scalar R (leqnn m).
have hb:0<b:=stiefel_gamma_volume_scalar_positive R (leqnn m).
have hbNe:b!=0 by rewrite gt_eqF //.
have hB:b*2!=0 by rewrite gt_eqF // mulr_gt0 // ltr0n.
have hRel:=@euclidean_stiefel_volume_exterior R n m hm hmn.
rewrite (@euclidean_grassmann_volume_orientation R n m hm hmn)
  (@euclidean_stiefel_gamma_volume R n m hmn)
  (@euclidean_stiefel_gamma_volume R m m (leqnn m)) muleA -!EFinM in hRel.
have hScaled:=congr1 (fun z : \bar R => ((b*2)^-1)%:E*z)%E hRel.
rewrite muleA -!EFinM mulVf // mul1e in hScaled.
have hRatio:(b*2)^-1*(2*a)=grassmann_gamma_volume_scalar R hmn.
  have hValue:a=b*grassmann_gamma_volume_scalar R hmn:=
    @stiefel_grassmann_gamma_scalar_identity R n m hmn.
  rewrite hValue; field; exact hbNe.
rewrite -hScaled hRatio.
reflexivity.
Qed.
