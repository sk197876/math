(** Federer 2.10.25, p. 189, first proof display: cancellation of
    the actual Gamma normalization in the fibre coefficient. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import RealHausdorffFibreCost RealHausdorffNormalisation
  RealPower RealPowerSuccessor EulerGamma EulerGammaHalfParameters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_hausdorff_fibre_constant_gamma]: supporting
    exact coefficient in Federer 2.10.25, pp. 188-189. Substituting
    alpha(t)=Gamma(1/2)^t/Gamma(t/2+1) cancels both the powers of
    Gamma(1/2) and the powers of two. The result is the original
    alpha(k)alpha(m)/alpha(k+m), times the m-th power of L, for
    every nonnegative real pair of degrees and every real L. *)
Lemma real_hausdorff_fibre_constant_gamma (R : realType) (k m : R)
    (hk : (0<=k)%R) (hm : (0<=m)%R) (L : R) :
    real_hausdorff_fibre_bound_constant hk hm L=
      real_power L m*euler_gamma (real_dimension_gamma_parameter (addr_ge0 hk hm))/
      (euler_gamma (real_dimension_gamma_parameter hk)*
        euler_gamma (real_dimension_gamma_parameter hm)).
Proof.
have hTwo : (0<2 :> R) by rewrite ltr0n.
have hHalf : (0<euler_gamma_half R) := euler_gamma_positive (positive_real_half R).
have hPk := real_power_strictly_positive k hTwo.
have hPm := real_power_strictly_positive m hTwo.
have hHk := real_power_strictly_positive k hHalf.
have hHm := real_power_strictly_positive m hHalf.
have hGk := euler_gamma_positive (real_dimension_gamma_parameter hk).
have hGm := euler_gamma_positive (real_dimension_gamma_parameter hm).
have hGsum := euler_gamma_positive (real_dimension_gamma_parameter (addr_ge0 hk hm)).
rewrite /real_hausdorff_fibre_bound_constant /real_hausdorff_normalisation
  (@real_power_add_exponents_positive R 2%R k m hTwo)
  (@real_power_add_exponents_positive R (euler_gamma_half R) k m hHalf).
field; by rewrite ?mulf_eq0 ?(gt_eqF hPk) ?(gt_eqF hPm)
  ?(gt_eqF hHk) ?(gt_eqF hHm) ?(gt_eqF hGk) ?(gt_eqF hGm) ?(gt_eqF hGsum).
Qed.
