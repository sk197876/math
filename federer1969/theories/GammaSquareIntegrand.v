(** Federer (1969), 3.2.13, p. 250: the
    square-substitution integrand exp(-y^2)|y|^(2s-1).
    Its prescribed value at zero is retained;
    an auxiliary zero completion is used only
    in the actual derivative calculation. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra ring.
From Federer Require Import EulerGammaUP EulerGammaBounds EulerGammaMeasurable RealPower
  RealPowerPositiveBaseIterate RealPowerSuccessor RealPowerContinuity RealExponentialUP RealExponentialSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [gamma_square_integrand]: the integral
    on the real line equalling Gamma(s),
    Federer 3.2.13, p. 250. The
    existing real-power convention includes 0^0= 1. *)
Definition gamma_square_integrand (R:realType) (s y:R):R:=
  RealExponential.exponential (-y^+2)*real_power `|y| (2*s-1).

(** Source for [gamma_square_zero_completion]: auxiliary zero
    completion at the single null point y= 0
    for the Gamma square substitution, Federer
    3.2.13, p. 250. It is
    not the final printed integrand when s= 1/2. *)
Definition gamma_square_zero_completion (R:realType) (s y:R):R:=
  if y== 0 then 0 else gamma_square_integrand s y.

(** Source for [gamma_square_integrand_nonnegative]: positivity
    of the Gaussian power integrand used in
    the Gamma substitution, Federer 3.2.13, p. 250. *)
Lemma gamma_square_integrand_nonnegative (R:realType) (s y:R):
  0<=gamma_square_integrand s y.
Proof.
apply:mulr_ge0; last exact:real_power_nonnegative.
exact:ltW (real_exponential_positive (@RealExponential.laws R) (-y^+2)).
Qed.

(** Source for [gamma_square_substitution_product]: the actual
    square-map Jacobian transforms exp(-x)x^(s-1)
    into twice the Gaussian power integrand,
    supporting Federer 3.2.13, p. 250.
    At y= 0 the auxiliary completion is zero;
    the final printed value is restored by null invariance. *)
Lemma gamma_square_substitution_product (R:realType) (s y:R):
  gamma_positive_completion s (y^+2)*(2*`|y|)= 2*gamma_square_zero_completion s y.
Proof.
case:(eqVneq y 0)=>[->|hy].
- by rewrite /gamma_positive_completion /gamma_square_zero_completion expr0n /= ltxx eqxx normr0 !mulr0.
- have hAbs:0<`|y| by rewrite normr_gt0.
  have hAbsSquare:y^+2=`|y|^+2 by rewrite -normrX ger0_norm ?sqr_ge0.
  have hSquare:0<y^+2 by rewrite hAbsSquare; exact (exprn_gt0 2 hAbs).
  have hPower:real_power (y^+2) (s-1)*`|y|=real_power `|y| (2*s-1).
    have hAdd:=@real_power_add_exponents_positive R `|y| (2*(s-1)) 1 hAbs.
    rewrite (real_power_one_exponent (normr_ge0 y)) in hAdd.
    rewrite hAbsSquare -real_power_two ?normr_ge0 //
      real_power_positive_base_iterate // -hAdd.
    congr (real_power _ _); ring.
  rewrite /gamma_positive_completion hSquare /gamma_square_zero_completion (negbTE hy)
    /euler_gamma_integrand /gamma_square_integrand.
  have hEq:RealExponential.exponential (-y^+2)*real_power (y^+2) (s-1)*(2*`|y|)=
    2*RealExponential.exponential (-y^+2)*(real_power (y^+2) (s-1)*`|y|) by ring.
  rewrite hEq hPower; ring.
Qed.
