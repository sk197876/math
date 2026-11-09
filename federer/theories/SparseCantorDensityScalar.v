(** Federer (1969), 3.3.21, p. 309: exact original low-density scalar quotient. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import RealPower RealPowerDivision RealPowerContinuity RealPowerSuccessor
  PositiveBaseRealPowerIteration.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [sparse_cantor_density_scalar_identity]: after
    actual original child-width and sparse-radius substitution, the
    real-degree density bound is a fixed finite coefficient times
    n^(2m-2), supporting 3.3.21, p. 309. All cancelled widths,
    Gamma coefficients, scales and subdivision denominators are
    explicitly positive. No asymptotic bound is an extra premise. *)
Theorem sparse_cantor_density_scalar_identity (R:realType) (m b k w N:R):
  0<m ->0<b ->0<k ->0<w ->0<N ->
  (b * real_power 2 m * real_power (w * real_power N (-m^-1)) (2 * m))/
    (b * real_power (2 * (k * w/(3 * N))) (2 * m))=
    (real_power 2 m * real_power (3/(2 * k)) (2 * m)) * real_power N (2 * m-2).
Proof.
move=>hm hb hk hw hN.
have hThree:0<(3:R) by rewrite ltr0n.
have hTwo:0<(2:R) by rewrite ltr0n.
have hR:0<2 * (k * w/(3 * N)) by rewrite mulr_gt0 // divr_gt0 // !mulr_gt0.
have hRoot:0<real_power N (-m^-1):=real_power_strictly_positive _ hN.
have hScalar:(w * real_power N (-m^-1))/(2 * (k * w/(3 * N)))=
    (3/(2 * k)) * (N * real_power N (-m^-1)).
  field;by rewrite ?gt_eqF // ?pnatr_eq0.
have hRatio:real_power (w * real_power N (-m^-1)) (2 * m)/
    real_power (2 * (k * w/(3 * N))) (2 * m)=
    real_power (3/(2 * k)) (2 * m) * real_power N (2 * m-2).
  rewrite -real_power_division ?mulr_ge0 ?ltW // hScalar.
  have hK0:0<= 3/(2 * k) by apply:ltW;rewrite divr_gt0 // mulr_gt0.
  rewrite real_power_product //;last by apply:mulr_ge0;exact:ltW.
  rewrite real_power_product ?ltW // positive_base_real_power_iteration //.
  have hExponent:(-m^-1) * (2 * m)= -2.
    field;by rewrite ?gt_eqF //.
  rewrite hExponent -real_power_add_exponents_positive //.
have hB:b!= 0 by rewrite gt_eqF.
have hPower:real_power (2 * (k * w/(3 * N))) (2 * m)!= 0
  by rewrite gt_eqF //;exact:real_power_strictly_positive.
have hFactor:(b * real_power 2 m * real_power (w * real_power N (-m^-1)) (2 * m))/
    (b * real_power (2 * (k * w/(3 * N))) (2 * m))=
    real_power 2 m * (real_power (w * real_power N (-m^-1)) (2 * m)/
      real_power (2 * (k * w/(3 * N))) (2 * m)).
  field;by rewrite hB hPower.
by rewrite hFactor hRatio mulrA.
Qed.
