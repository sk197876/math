(** Federer (1969), 3.2.13, p. 250: after including
    the polar factor r^(m-1), the radial exponent is 2 sum(z)-1. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets ring lra.
From Federer Require Import GaussianPolarSeparation GammaSquareIntegrand RealPower
  RealPowerSuccessor RealPowerNaturalHausdorff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [gaussian_coordinate_exponent_sum]: addition of
    the m coordinate exponents in Federer 3.2.13, p. 250. *)
Lemma gaussian_coordinate_exponent_sum (R:realType) m (z:'I_m->R):
  (\sum_j (2*z j-1))= 2*(\sum_j z j)-m%:R.
Proof.
rewrite sumrB -mulr_sumr sumr_const card_ord.
by rewrite -mulr_natr mul1r.
Qed.

(** Source for [gaussian_weighted_radial_factor]: the actual
    radial integrand after angular separation, Federer 3.2.13,
    p. 250, equals the Gaussian Gamma integrand at sum(z). *)
Lemma gaussian_weighted_radial_factor (R:realType) m (z:'I_m->R) (r:R):
  (0<m)%N ->0<r ->
  gaussian_radial_factor z r*r^+(m-1)=gamma_square_integrand (\sum_j z j) r.
Proof.
move=>hm hr.
have hDim:((m-1)%:R:R)+1=m%:R.
  have hNat:(m-1+1=m)%N:=subnK hm.
  have hCast:=congr1 (fun k:nat=>(k%:R:R)) hNat.
  rewrite natrD in hCast.
  exact hCast.
have hExp:(\sum_j (2*z j-1))+(m-1)%:R= 2*(\sum_j z j)-1.
  rewrite gaussian_coordinate_exponent_sum; have hPred:((m-1)%:R:R)=m%:R-1 by lra.
  rewrite hPred; ring.
rewrite /gaussian_radial_factor /gamma_square_integrand (ger0_norm (ltW hr))
  -(@real_power_natural_exponent R r (m-1) (ltW hr)) -mulrA
  -real_power_add_exponents_positive // hExp.
by [].
Qed.
