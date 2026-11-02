(** Federer (1969), 3.2.28(5), p. 267:
    the scalar in the printed Stiefel volume formula
    satisfies the actual coarea recurrence. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import EulerGamma EulerGammaHalfParameters StiefelGammaProduct
  RealPower RealPowerSuccessor RealPowerNaturalHausdorff RealPowerHalfNatural.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [stiefel_gamma_volume_scalar]: the exact
    scalar 2^(m(m+3)/4) Gamma(1/2)^(m(2n-m+1)/2)
    divided by the printed Gamma product, Federer
    3.2.28(5), p. 267. Both exponentials use
    real exponents and the actual Euler Gamma values. *)
Definition stiefel_gamma_volume_scalar (R:realType) n m (hmn:(m<=n)%N):R:=
  real_power 2 (m%:R*(m%:R+3)/4)*
  real_power (euler_gamma_half R) (m%:R*(2*n%:R-m%:R+1)/2)/
  stiefel_gamma_product R hmn.

(** Source for [stiefel_gamma_volume_scalar_positive]: every
    factor of the volume scalar in Federer 3.2.28(5),
    p. 267, is positive in its printed range. *)
Lemma stiefel_gamma_volume_scalar_positive (R:realType) n m (hmn:(m<=n)%N):
  0<stiefel_gamma_volume_scalar R hmn.
Proof.
apply:divr_gt0; last exact:stiefel_gamma_product_positive.
apply:mulr_gt0; apply:real_power_strictly_positive.
- by rewrite ltr0n.
- exact:euler_gamma_positive.
Qed.

(** Source for [stiefel_gamma_volume_scalar_zero]: the
    empty-product extension of the displayed formula,
    Federer 3.2.28(5), p. 267. *)
Lemma stiefel_gamma_volume_scalar_zero (R:realType) n (h:(0<=n)%N):
  stiefel_gamma_volume_scalar R h= 1.
Proof.
by rewrite /stiefel_gamma_volume_scalar !mul0r !real_power_zero_exponent
  stiefel_gamma_product_zero !mul1r invr1.
Qed.

(** Source for [stiefel_gamma_volume_scalar_successor]: the
    induction arithmetic in Federer 3.2.28(5),
    p. 267, using the sphere Gamma value
    from 3.2.13, p. 251, and the exact
    (sqrt 2)^k factor from the forgetful map. *)
Lemma stiefel_gamma_volume_scalar_successor (R:realType) n k
    (hkn:(k.+1<=n)%N) (hk:(k<=n)%N) (hPos:(0<n-k)%N):
  stiefel_gamma_volume_scalar R hkn=
    (Num.sqrt (2:R))^+k*
    (2*(euler_gamma_half R)^+(n-k)/euler_gamma (@positive_dimension_half R (n-k) hPos))*
    stiefel_gamma_volume_scalar R hk.
Proof.
have h2:0<(2:R) by rewrite ltr0n.
have hG:0<euler_gamma_half R:=euler_gamma_positive _.
have hExponent2:
    (k.+1)%:R*((k.+1)%:R+3)/4=(k%:R/2+1)+k%:R*(k%:R+3)/4 :> R.
  rewrite -[k.+1]addn1 natrD; field; lra.
have hExponentG:
    (k.+1)%:R*(2*n%:R-(k.+1)%:R+1)/2=(n-k)%N%:R+k%:R*(2*n%:R-k%:R+1)/2 :> R.
  rewrite -[k.+1]addn1 natrD natrB //; field; lra.
have hPower2:
    real_power 2 ((k.+1)%:R*((k.+1)%:R+3)/4)=
      (Num.sqrt (2:R))^+k*2*real_power 2 (k%:R*(k%:R+3)/4).
  rewrite hExponent2 !real_power_add_exponents_positive //
    real_power_half_natural // real_power_one_exponent //.
have hPowerG:
    real_power (euler_gamma_half R) ((k.+1)%:R*(2*n%:R-(k.+1)%:R+1)/2)=
      (euler_gamma_half R)^+(n-k)*real_power (euler_gamma_half R) (k%:R*(2*n%:R-k%:R+1)/2).
  rewrite hExponentG (@real_power_add_exponents_positive R (euler_gamma_half R)
    (n-k)%N%:R (k%:R*(2*n%:R-k%:R+1)/2) hG)
    (@real_power_natural_exponent R (euler_gamma_half R) (n-k) (ltW hG)).
  reflexivity.
have hPi:stiefel_gamma_product R hk!=0 by rewrite gt_eqF //; exact:stiefel_gamma_product_positive.
have hGamma:euler_gamma (@positive_dimension_half R (n-k) hPos)!=0 by rewrite gt_eqF //; exact:euler_gamma_positive.
rewrite /stiefel_gamma_volume_scalar hPower2 hPowerG
  (@stiefel_gamma_product_successor R n k hkn hk hPos).
field; by rewrite ?mulf_eq0 ?(negbTE hPi) ?(negbTE hGamma).
Qed.
