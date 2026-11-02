(** Federer (1969), 2.10.28, final sentence p. 193: m=log(2)/log(3) and
    n_j=2 produce the middle-third Cantor construction. Verify the positive
    exponent below one and the exact child length d/3 and spacing 2d/3 from
    the abstract split laws. The PDF was checked directly: its exponent is
    the same logarithm ratio. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealExponentialUP RealExponentialSealed RealExponentialLaws
  RealPower RealPowerDivision CantorSplitRadiusUP CantorSplitRadius PowerConcaveIntervalGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [classical_cantor_exponent]: direct
    m=log(2)/log(3) in the final sentence
    of 2.10.28, p. 193. The logarithm
    is the project's sealed real logarithm. *)
Definition classical_cantor_exponent (R : realType) :=
  @RealExponential.logarithm R 2 / @RealExponential.logarithm R 3.

(** Source for [classical_cantor_exponent_bounds]: supporting
    0<m<1 for the classical case of
    2.10.28, p. 193, required to
    apply the fractional power-gauge theorem. *)
Lemma classical_cantor_exponent_bounds (R : realType) :
  0<@classical_cantor_exponent R /\ @classical_cantor_exponent R<1.
Proof.
have hL2 : (0<@RealExponential.logarithm R 2)%R.
  rewrite -(real_exponential_strict_order (@RealExponential.laws R))
    (real_exponential_zero (@RealExponential.laws R))
    (real_exponential_logarithm (@RealExponential.laws R)); lra.
have hL3 : (0<@RealExponential.logarithm R 3)%R.
  rewrite -(real_exponential_strict_order (@RealExponential.laws R))
    (real_exponential_zero (@RealExponential.laws R))
    (real_exponential_logarithm (@RealExponential.laws R)); lra.
have h23 : (@RealExponential.logarithm R 2<@RealExponential.logarithm R 3)%R.
  rewrite -(real_exponential_strict_order (@RealExponential.laws R))
    !(real_exponential_logarithm (@RealExponential.laws R)); lra.
rewrite /classical_cantor_exponent; split; first by rewrite divr_gt0.
by rewrite ltr_pdivrMr // mul1r.
Qed.

(** Source for [classical_cantor_power_three]: supporting 3^m=2 calculation
    for the classical middle-third split in 2.10.28, p. 193 *)
Lemma classical_cantor_power_three (R : realType) :
  real_power (3 : R) (@classical_cantor_exponent R) = 2.
Proof.
have hthree : (0<3 :> R) by lra.
have htwo : (0<2 :> R) by lra.
have hL3 : (@RealExponential.logarithm R 3!=0)%R.
  apply/eqP=> he.
  have hh := @real_exponential_logarithm R _ _ (@RealExponential.laws R) 3 hthree.
  rewrite he (real_exponential_zero (@RealExponential.laws R)) in hh; lra.
rewrite real_power_positive_base // /classical_cantor_exponent divfK //.
exact (@real_exponential_logarithm R _ _ (@RealExponential.laws R) 2 htwo).
Qed.

(** Source for [classical_cantor_split_parameters]: direct s=d/3 and t=2d/3
    for the classical case of 2.10.28, p. 193 Uniqueness identifies the
    sealed radius from its laws, without computing through the IVT existence
    construction. *)
Theorem classical_cantor_split_parameters (R : realType) (c d : R)
    (hc : 0<c) (hd : 0<d) :
  let m := @classical_cantor_exponent R in
  let hg := @power_concave_interval_gauge R c m hc
    (classical_cantor_exponent_bounds R).1 (classical_cantor_exponent_bounds R).2 in
  @cantor_split_radius R (fun t=>c*real_power t m) hg d 2 hd (leqnn 2)=d/3 /\
  cantor_split_spacing d 2 (d/3) = 2*d/3.
Proof.
move=> m hg.
have hthree : (0<3 :> R) by lra.
have hthird : is_cantor_split_radius (fun t=>c*real_power t m) d 2 (d/3).
  constructor.
  - split; lra.
  - rewrite (@real_power_division R d 3 m (ltW hd) hthree) classical_cantor_power_three; by lra.
have hden : (2%:R-1 : R) = 1 by lra.
split; last by rewrite /cantor_split_spacing hden divr1; lra.
apply: (@cantor_split_radius_unique R _ hg d 2 _ (d/3)
  (@cantor_split_radius_specification R _ hg d 2 hd (leqnn 2)) hthird).
Qed.
