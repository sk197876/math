(** Federer (1969), 2.4.14, p. 88: the signed powers |f|^p sign f in the
    equality condition. These supporting scalar laws identify the sign with
    Federer's convention in 2.1.1, p. 51, and retain the value zero at zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import RealPower ExtendedRealPartial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_extended_sign_sgr]: identification of
    the scalar sign in Federer 2.4.14, p. 88,
    with his definition in 2.1.1, p. 51. *)
Lemma finite_extended_sign_sgr (R : realType) (x : R) :
  extended_sign x%:E = Num.sg x.
Proof.
rewrite /extended_sign !lte_fin.
have [hx|hx|hx] := ltgtP 0 x.
- by rewrite (gtr0_sg hx).
- by rewrite (ltr0_sg hx).
- by rewrite -hx sgr0.
Qed.

(** Source for [signed_real_power]: the scalar expression |f|^p sign f in
    the equality criterion of Federer 2.4.14, p. 88 *)
Definition signed_real_power (R : realType) (p x : R) :=
  real_power `|x| p * Num.sg x.

(** Source for [signed_real_power_zero]: supporting zero-value
    convention for the equality case of Federer 2.4.14,
    p. 88, including the auxiliary exponent-zero case. *)
Lemma signed_real_power_zero (R : realType) (p : R) :
  signed_real_power p 0 = 0.
Proof. by rewrite /signed_real_power sgr0 mulr0. Qed.

(** Source for [signed_real_power_negate]: sign reversal in
    the signed-power dependence criterion of Federer 2.4.14,
    p. 88. *)
Lemma signed_real_power_negate (R : realType) (p x : R) :
  signed_real_power p (-x) = -signed_real_power p x.
Proof. by rewrite /signed_real_power normrN sgrN mulrN. Qed.

(** Source for [signed_real_power_positive_scale]: supporting recovery of
    the original signed powers from the normalised functions in Federer
    2.4.14, proof p. 88 *)
Lemma signed_real_power_positive_scale (R : realType) (p c x : R) :
  0 < c -> signed_real_power p (c*x) = real_power c p * signed_real_power p x.
Proof.
move=> hc; rewrite /signed_real_power normrM (ger0_norm (ltW hc))
  (@real_power_product R c `|x| p (ltW hc) (normr_ge0 x)) sgrM (gtr0_sg hc) mul1r.
by rewrite mulrA.
Qed.

(** Source for [signed_real_power_absolute]: absolute value
    of the signed power in Federer 2.4.14, p. 88.
    The positive-exponent hypothesis gives the required zero
    value when x vanishes. *)
Lemma signed_real_power_absolute (R : realType) (p x : R) :
  0 < p -> `|signed_real_power p x| = real_power `|x| p.
Proof.
move=> hp; have [->|hx] := eqVneq x 0.
- by rewrite signed_real_power_zero normr0 real_power_zero_base ?gt_eqF.
- by rewrite /signed_real_power normrM (ger0_norm (real_power_nonnegative _ _)) normr_sg hx mulr1.
Qed.
