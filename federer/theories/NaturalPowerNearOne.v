(** Federer (1969), 3.2.46, pp. 281–282: the
    local distortion factor may be taken arbitrarily close
    to one. This scalar support lemma uses the actual
    positive real power already developed for 2.4.12. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealPower RealPowerNaturalHausdorff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [natural_power_factor_near_one]: arbitrarily
    small multiplicative distortion in the local-isometry
    reduction of 3.2.46, pp. 281–282. The zero
    exponent has the exact factor one. No scalar sequence
    or global family of local factors is selected. *)
Lemma natural_power_factor_near_one (R : realType) k (c e : R) :
  0<=c -> 0<e -> exists lambda : R, 1<lambda /\
    1<=lambda^+k /\ lambda^+k<=2 /\ (lambda^+k-1)*(c+1)<e/4.
Proof.
move=> hc he.
case:k=> [|k].
- exists 2; split; first by rewrite ltr1n.
  rewrite expr0 subrr mul0r; split; first exact: lexx.
  split; first by rewrite ler1n.
  by rewrite divr_gt0 // ltr0n.
- have hc1 : 0<c+1 by lra.
  have hFour : 0<(4:R) by rewrite ltr0n.
  have hEight : 0<(8:R) by rewrite ltr0n.
  have hEightInv : 0<(8:R)^-1 by rewrite invr_gt0.
  pose d := Num.min 1 (e/(c+1))/8.
  have hd : 0<d by rewrite /d divr_gt0 // lt_min ltr01 divr_gt0.
  have hd1 : d<=1/8.
    apply:ler_wpM2r; first exact:ltW hEightInv.
    by rewrite ge_min lexx.
  have hde : d*(c+1)<=e/8.
    have hMin : Num.min 1 (e/(c+1))<=e/(c+1) by rewrite ge_min lexx orbT.
    have hMul := ler_wpM2r (ltW hc1) hMin.
    rewrite divfK ?gt_eqF // in hMul.
    have hDiv := ler_wpM2r (ltW hEightInv) hMul.
    have hEq : Num.min 1 (e/(c+1))*(c+1)/8=d*(c+1) by rewrite /d mulrAC.
    by rewrite hEq in hDiv.
  have hBase : 1<1+d by rewrite ltrDl.
  have hBase0 : 0<1+d := lt_trans ltr01 hBase.
  have hk : 0<(k.+1%:R:R) by rewrite ltr0n.
  have hki : 0<(k.+1%:R:R)^-1 by rewrite invr_gt0.
  pose lambda := real_power (1+d) (k.+1%:R:R)^-1.
  have hLambda : 1<lambda.
    have hh := real_power_strict_monotone ler01 hBase hki.
    by rewrite real_power_one_base in hh.
  have hPower : lambda^+k.+1= 1+d.
    rewrite -(real_power_natural_exponent k.+1 (ltW (lt_trans ltr01 hLambda))).
    rewrite /lambda (@real_power_positive_iterate R (1+d) (k.+1%:R:R)^-1
      (k.+1%:R:R) (ltW hBase0) hki hk).
    rewrite mulVf ?gt_eqF //; exact:real_power_one_exponent (ltW hBase0).
  exists lambda; split; first exact hLambda.
  rewrite hPower; split; first by lra.
  split; first by lra.
  have hCancel : (e/8)*8=e by rewrite divfK ?pnatr_eq0.
  have hCancel4 : (e/4)*4=e by rewrite divfK ?pnatr_eq0.
  nra.
Qed.
