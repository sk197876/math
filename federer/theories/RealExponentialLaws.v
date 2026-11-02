(** Scalar background for Federer (1969), 2.4.12, pp. 86–87, and 2.4.13, p.
    88: real powers, exponential and logarithm. These supporting scalar laws
    are not additional numbered claims in Federer. Existence is proved
    separately; downstream arguments use the abstract laws through an opaque
    seal. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealExponentialUP RealExponentialSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Laws.
Variable R : realType.
Local Notation E := (@RealExponential.exponential R).
Local Notation L := (@RealExponential.logarithm R).
Local Notation h := (@RealExponential.laws R).

(** Source for [real_exponential_injective]: supporting elementary
    scalar fact for applying exp in Federer 2.4.13, p. 88. *)
Lemma real_exponential_injective : injective E.
Proof. move=> x y he; by rewrite -(real_logarithm_exponential h x) he (real_logarithm_exponential h). Qed.

(** Source for [real_exponential_order]: supporting non-strict
    order preservation for Federer 2.4.13, p. 88. *)
Lemma real_exponential_order x y : (E x <= E y) = (x <= y).
Proof. by rewrite leNgt (real_exponential_strict_order h) -leNgt. Qed.

(** Source for [real_logarithm_one]: elementary scalar
    normalisation supporting Federer 2.4.13, p. 88. *)
Lemma real_logarithm_one : L 1 = 0.
Proof. by rewrite -(real_exponential_zero h) (real_logarithm_exponential h). Qed.

(** Source for [real_logarithm_product]: supporting scalar
    law for real powers in Federer 2.4.12–13, pp. 86–88. *)
Lemma real_logarithm_product x y : 0 < x -> 0 < y -> L (x*y) = L x + L y.
Proof.
move=> hx hy; apply: real_exponential_injective.
by rewrite (real_exponential_add h) !(real_exponential_logarithm h) // mulr_gt0.
Qed.

(** Source for [real_logarithm_order]: scalar monotonicity
    supporting the logarithmic proof in Federer 2.4.13, p. 88. *)
Lemma real_logarithm_order x y : 0 < x -> 0 < y -> (L x <= L y) = (x <= y).
Proof. by move=> hx hy; rewrite -real_exponential_order !(real_exponential_logarithm h). Qed.

(** Source for [real_logarithm_tangent]: supporting bound
    log(x) <= x-1 for the strict-concavity argument in
    Federer 2.4.13, p. 88; derived from the exponential tangent. *)
Lemma real_logarithm_tangent x : 0 < x -> L x <= x-1.
Proof.
move=> hx; have hb := real_exponential_tangent h (L x).
rewrite lerBrDl; by rewrite (real_exponential_logarithm h) in hb.
Qed.

(** Source for [real_logarithm_strict_tangent]: strict version
    away from one, supporting equality in Federer 2.4.13,
    p. 88. This is an intermediate scalar lemma. *)
Lemma real_logarithm_strict_tangent x : 0 < x -> x != 1 -> L x < x-1.
Proof.
move=> hx hx1; have hl : L x != 0.
  apply/negP=> /eqP he; have he' := real_exponential_logarithm h hx.
  by rewrite he (real_exponential_zero h) in he'; move: hx1; rewrite -he' eqxx.
have hb := real_exponential_strict_tangent h hl.
rewrite ltrBrDl; by rewrite (real_exponential_logarithm h) in hb.
Qed.
End Laws.

(** Source for [real_logarithm_inverse]: elementary reciprocal
    identity supporting the logarithmic proof of Federer 2.4.13,
    p. 88, derived from the abstract scalar laws. *)
Lemma real_logarithm_inverse (R : realType) (x : R) : 0 < x ->
  RealExponential.logarithm x^-1 = - RealExponential.logarithm x.
Proof.
move=> hx; apply: (addrI (RealExponential.logarithm x)).
by rewrite -real_logarithm_product ?invr_gt0 // mulfV ?gt_eqF // real_logarithm_one addrN.
Qed.

(** Source for [real_logarithm_ratio]: elementary quotient
    identity supporting the strict-concavity argument of
    Federer 2.4.13, p. 88. *)
Lemma real_logarithm_ratio (R : realType) (x y : R) : 0 < x -> 0 < y ->
  RealExponential.logarithm (x/y) = RealExponential.logarithm x - RealExponential.logarithm y.
Proof. by move=> hx hy; rewrite real_logarithm_product ?invr_gt0 // real_logarithm_inverse. Qed.
