(** Federer (1969), 3.2.28(5), p. 267:
    the Grassmann Gamma quotient obtained by dividing
    the two actual Stiefel volume formulas. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import EulerGamma EulerGammaHalfParameters StiefelGammaProduct StiefelGammaVolumeScalar
  RealPower RealPowerSuccessor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [grassmann_gamma_volume_scalar]: the second
    displayed scalar in Federer 3.2.28(5), p. 267.
    The numerator product Gamma(j/2), 1<=j<=m,
    is indexed in reverse order as Gamma((m-i)/2),
    0<=i<m; no value or normalization is changed. *)
Definition grassmann_gamma_volume_scalar (R:realType) n m (hmn:(m<=n)%N):R:=
  real_power (euler_gamma_half R) (m%:R * (n%:R-m%:R))*
  stiefel_gamma_product R (leqnn m)/stiefel_gamma_product R hmn.

(** Source for [grassmann_gamma_volume_scalar_positive]:
    all factors in the Grassmann volume formula,
    Federer 3.2.28(5), p. 267, are positive. *)
Lemma grassmann_gamma_volume_scalar_positive (R:realType) n m (hmn:(m<=n)%N):
  0<grassmann_gamma_volume_scalar R hmn.
Proof.
apply:divr_gt0; last exact:stiefel_gamma_product_positive.
apply:mulr_gt0; last exact:stiefel_gamma_product_positive.
apply:real_power_strictly_positive; exact:euler_gamma_positive.
Qed.

(** Source for [stiefel_grassmann_gamma_scalar_identity]:
    division of the two Stiefel scalars yields the
    Grassmann scalar in Federer 3.2.28(5), p. 267.
    The 2-powers cancel, leaving Gamma(1/2)^(m(n-m)). *)
Lemma stiefel_grassmann_gamma_scalar_identity (R:realType) n m (hmn:(m<=n)%N):
  stiefel_gamma_volume_scalar R hmn=
    stiefel_gamma_volume_scalar R (leqnn m)*grassmann_gamma_volume_scalar R hmn.
Proof.
have hG:0<euler_gamma_half R:=euler_gamma_positive _.
have hExponent:m%:R * (2 * n%:R-m%:R+1)/2=
    m%:R * (2 * m%:R-m%:R+1)/2+m%:R * (n%:R-m%:R) :> R.
  field; lra.
have hPi:stiefel_gamma_product R hmn!=0 by rewrite gt_eqF //; exact:stiefel_gamma_product_positive.
have hPm:stiefel_gamma_product R (leqnn m)!=0 by rewrite gt_eqF //; exact:stiefel_gamma_product_positive.
rewrite /stiefel_gamma_volume_scalar /grassmann_gamma_volume_scalar hExponent
  real_power_add_exponents_positive //.
field; by rewrite ?mulf_eq0 ?(negbTE hPi) ?(negbTE hPm).
Qed.
