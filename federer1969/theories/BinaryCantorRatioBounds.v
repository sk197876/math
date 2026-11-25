(** Federer (1969), 3.3.20, pp. 306–307: actual binary side-ratio bounds. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import RealPower RealPowerContinuity RealExponentialUP RealExponentialSealed
  RealExponentialLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [binary_base_power_strict_exponent_order]: supporting
    strict order of the actual base-two powers used in 3.3.20,
    pp. 306–307. The existing sealed logarithm and exponential prove it. *)
Lemma binary_base_power_strict_exponent_order (R:realType) (p q:R):
  (real_power (2:R) p<real_power 2 q)=(p<q).
Proof.
have hTwo:(0<2:>R) by rewrite ltr0n.
have hLog:(0<@RealExponential.logarithm R 2).
  rewrite -(real_exponential_strict_order (@RealExponential.laws R))
    (real_exponential_zero (@RealExponential.laws R))
    (real_exponential_logarithm (@RealExponential.laws R));lra.
by rewrite !real_power_positive_base //
  (real_exponential_strict_order (@RealExponential.laws R)) ltr_pM2r.
Qed.

(** Source for [binary_cantor_original_ratio_bounds]: the original
    lambda= 2^(-1/m) lies strictly between zero and one half for
    0<m<1, and strictly above one quarter for m>1/2. These are the
    actual side bounds underlying the projection overlap locus and its
    nonempty interior in 3.3.20, pp. 306–307. *)
Theorem binary_cantor_original_ratio_bounds (R:realType) (m:R):
  0<m ->m<1 ->
  (0<real_power 2 (-m^-1)<1/2) /\
  (1/2<m ->1/4<real_power 2 (-m^-1)).
Proof.
move=>hm hm1.
have hTwo:(0<2:>R) by rewrite ltr0n.
have hM:m!= 0 by rewrite gt_eqF.
have hCancel:m * m^-1= 1 by rewrite mulfV.
have hInversePositive:0<m^-1 by rewrite invr_gt0.
have hInverseLower:1<m^-1 by nra.
have hHalf:real_power (2:R) (-1)= 1/2.
  by rewrite real_power_negative_exponent // real_power_one_exponent ?ltW // mul1r.
have hQuarter:real_power (2:R) (-2)= 1/4.
  rewrite real_power_negative_exponent // real_power_two ?ltW //.
  have hSquare:(2:R)^+2= 4 by ring.
  by rewrite hSquare mul1r.
split.
- apply/andP;split;first exact:real_power_strictly_positive.
  rewrite -hHalf binary_base_power_strict_exponent_order;by nra.
- move=>hSuper;rewrite -hQuarter binary_base_power_strict_exponent_order.
  have hInverseUpper:m^-1<2 by nra.
  by nra.
Qed.
