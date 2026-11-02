(** Federer (1969), 2.4.16, pp. 89–90: the attaining test u =
    (|f|/phi_p(f))^(p-1) sign(f), for finite p>1 and positive finite norm.
    These are scalar supporting identities; existence of the test as an Lq
    function and the supremum assertion are separate theorems. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealPower RealPowerDivision RealPowerSuccessor ConjugateExponents.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [dual_power_test]: the displayed attaining test
    in Federer 2.4.16, p. 89, with supplied positive norm a. *)
Definition dual_power_test (R : realType) (p a x : R) :=
  real_power (`|x|/a) (p-1) * Num.sg x.

(** Source for [dual_power_test_absolute]: absolute-value
    computation supporting Federer 2.4.16, pp. 89–90. *)
Lemma dual_power_test_absolute (R : realType) (p a x : R) :
  1 < p -> 0 < a -> `|dual_power_test p a x| = real_power (`|x|/a) (p-1).
Proof.
move=> hp ha; have hd : 0 < p-1 by rewrite subr_gt0.
have [->|hx] := eqVneq x 0.
- by rewrite /dual_power_test sgr0 mulr0 !normr0 mul0r real_power_zero_base ?gt_eqF.
- by rewrite /dual_power_test normrM (ger0_norm (real_power_nonnegative _ _)) normr_sg hx mulr1.
Qed.

(** Source for [dual_power_test_conjugate_power]: the identity
    |u|^q=(|f|/phi_p(f))^p in Federer 2.4.16, p. 89. *)
Lemma dual_power_test_conjugate_power (R : realType) (p a x : R) :
  1 < p -> 0 < a ->
  real_power `|dual_power_test p a x| (finite_conjugate_exponent p) = real_power (`|x|/a) p.
Proof.
move=> hp ha; have hd : 0 < p-1 by rewrite subr_gt0.
have hx : 0 <= `|x|/a by rewrite divr_ge0 //; exact: ltW ha.
have hq := lt_trans (ltr01) (finite_conjugate_exponent_strict hp).
by rewrite dual_power_test_absolute // real_power_positive_iterate // finite_conjugate_exponent_product.
Qed.

(** Source for [dual_power_test_sign]: the sign requirement
    for the attaining test in Federer 2.4.16, p. 89, including f=0. *)
Lemma dual_power_test_sign (R : realType) (p a x : R) :
  1 < p -> 0 < a -> Num.sg (dual_power_test p a x) = Num.sg x.
Proof.
move=> hp ha; have [->|hx] := eqVneq x 0.
- by rewrite /dual_power_test sgr0 mulr0 sgr0.
have hxpos : 0 < `|x|/a by rewrite divr_gt0 // normr_gt0.
have hpow := @real_power_strictly_positive R (`|x|/a) (p-1) hxpos.
by rewrite /dual_power_test sgrM (gtr0_sg hpow) mul1r sgr_id.
Qed.

(** Source for [dual_power_test_product]: the integrand identity
    fu=|f|^p/phi_p(f)^(p-1), Federer 2.4.16, p. 89. *)
Lemma dual_power_test_product (R : realType) (p a x : R) :
  1 < p -> 0 < a ->
  x * dual_power_test p a x = real_power `|x| p / real_power a (p-1).
Proof.
move=> hp ha; have hd : 0 < p-1 by rewrite subr_gt0.
rewrite /dual_power_test real_power_division ?normr_ge0 //.
rewrite mulrCA [x * Num.sg x]mulrC -normrEsg.
rewrite mulrAC.
have he : p = (p-1)+1 by rewrite subrK.
have hh := @real_power_positive_successor R `|x| (p-1) (normr_ge0 x) hd.
by rewrite -he in hh; rewrite hh.
Qed.
