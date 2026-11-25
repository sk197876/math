(** Federer (1969), 3.4.4, p. 318: the exact
    relation between the two original interval scales. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import RealPower RealPowerPositiveBaseIterate RealPowerNaturalHausdorff
  PowerCantorUniformGapScalar.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [binary_cantor_scale_bounds]: the positive
    strict gap of the original binary Cantor intervals,
    3.4.4, p. 318. Both the contraction and
    the gap follow from the original dimension parameter. *)
Lemma binary_cantor_scale_bounds (R:realType) (alpha:R):
  0<alpha ->alpha<1 ->0<real_power 2 (-alpha^-1)<1 /\
    0<1-2*real_power 2 (-alpha^-1).
Proof.
move=>hAlpha hAlphaUpper.
have hTwo:0<(2:R) by rewrite ltr0n.
have hPositive:=@real_power_strictly_positive R 2 (-alpha^-1) hTwo.
have hGap:0<1-2*real_power 2 (-alpha^-1):=(andP (power_cantor_uniform_gap_positive hAlpha hAlphaUpper)).1.
split=>//;apply/andP;split=>//;nra.
Qed.

(** Source for [binary_cantor_scale_power]: the exact
    powers 2^(-j/alpha) and 2^(-j/beta) in
    3.4.4, p. 318. Their ratio of exponents
    is alpha/beta, at every original finite level. *)
Lemma binary_cantor_scale_power (R:realType) (alpha beta:R):
  0<alpha ->0<beta ->forall j,
  (real_power 2 (-beta^-1))^+j=
    real_power ((real_power 2 (-alpha^-1))^+j) (alpha/beta).
Proof.
move=>hAlpha hBeta j.
have hTwo:0<(2:R) by rewrite ltr0n.
have hRho:=@real_power_strictly_positive R 2 (-alpha^-1) hTwo.
have hSigma:=@real_power_strictly_positive R 2 (-beta^-1) hTwo.
rewrite -(@real_power_natural_exponent R (real_power 2 (-beta^-1)) j (ltW hSigma))
  -(@real_power_natural_exponent R (real_power 2 (-alpha^-1)) j (ltW hRho)).
rewrite !real_power_positive_base_iterate //.
congr (real_power 2 _).
have hANe:alpha!=0 by rewrite gt_eqF.
have hBNe:beta!=0 by rewrite gt_eqF.
field; by rewrite ?gt_eqF.
Qed.
