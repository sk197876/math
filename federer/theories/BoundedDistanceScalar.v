(** Federer (1969), 2.2.6, p. 63: each coordinate distance t is replaced by
    t/(1+t) in the displayed metric. We prove the needed scalar laws
    locally. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [bounded_distance_scalar]: Federer 2.2.6,
    p. 63, supporting scalar expression t/(1+t) in the coordinate
    metric; it will only be used on nonnegative distances. *)
Definition bounded_distance_scalar (R : realType) (t : R) := t / (1 + t).

(** Source for [bounded_distance_scalar_nonnegative]: Federer 2.2.6, p. 63,
    supporting nonnegativity of each normalised coordinate distance *)
Lemma bounded_distance_scalar_nonnegative (R : realType) (t : R) :
  0 <= t -> 0 <= bounded_distance_scalar t.
Proof. move=> ht; apply: divr_ge0=> //; exact: addr_ge0 ler01 ht. Qed.

(** Source for [bounded_distance_scalar_lt_one]: Federer
    2.2.6, p. 63, supporting strict bound by one for the
    coordinate transform, used to bound the weighted series. *)
Lemma bounded_distance_scalar_lt_one (R : realType) (t : R) :
  0 <= t -> bounded_distance_scalar t < 1.
Proof.
move=> ht; have hd : 0 < 1 + t.
  apply: lt_le_trans ltr01 _; by rewrite lerDl.
by rewrite /bounded_distance_scalar ltr_pdivrMr // mul1r ltrDr ltr01.
Qed.

(** Source for [bounded_distance_scalar_zero]: Federer 2.2.6,
    p. 63, the normalised distance vanishes on equal coordinates. *)
Lemma bounded_distance_scalar_zero (R : realType) : bounded_distance_scalar (0 : R) = 0.
Proof. by rewrite /bounded_distance_scalar mul0r. Qed.

(** Source for [bounded_distance_scalar_eq_zero]: Federer 2.2.6, p. 63,
    supporting separation: a nonnegative coordinate distance has zero
    transform exactly when it is zero. *)
Lemma bounded_distance_scalar_eq_zero (R : realType) (t : R) :
  0 <= t -> (bounded_distance_scalar t == 0) = (t == 0).
Proof.
move=> ht; have hd : 0 < 1 + t.
  apply: lt_le_trans ltr01 _; by rewrite lerDl.
by rewrite /bounded_distance_scalar mulf_eq0 invr_eq0 (gt_eqF hd) orbF.
Qed.

(** Source for [bounded_distance_scalar_monotone]: Federer 2.2.6, p. 63,
    supporting monotonicity of the coordinate transform *)
Lemma bounded_distance_scalar_monotone (R : realType) (x y : R) :
  0 <= x -> x <= y -> bounded_distance_scalar x <= bounded_distance_scalar y.
Proof.
move=> hx hxy; have hy : 0 <= y := le_trans hx hxy.
have hdx : 0 < 1 + x.
  apply: lt_le_trans ltr01 _; by rewrite lerDl.
have hdy : 0 < 1 + y.
  apply: lt_le_trans ltr01 _; by rewrite lerDl.
rewrite /bounded_distance_scalar ler_pdivrMr // mulrAC ler_pdivlMr //.
by rewrite !mulrDr !mulr1 (mulrC y x) lerD2r.
Qed.

(** Source for [bounded_distance_scalar_subadditive]: Federer 2.2.6, p. 63,
    supporting triangle inequality of the bounded coordinate distance.
    Divide each summand by the larger denominator 1+x+y and compare it with
    its own denominator. *)
Lemma bounded_distance_scalar_subadditive (R : realType) (x y : R) :
  0 <= x -> 0 <= y ->
  bounded_distance_scalar (x + y) <= bounded_distance_scalar x + bounded_distance_scalar y.
Proof.
move=> hx hy.
have hdx : 0 < 1 + x.
  apply: lt_le_trans ltr01 _; by rewrite lerDl.
have hdy : 0 < 1 + y.
  apply: lt_le_trans ltr01 _; by rewrite lerDl.
have hd : 0 < 1 + (x + y).
  apply: lt_le_trans ltr01 _; rewrite lerDl; exact: addr_ge0 hx hy.
rewrite /bounded_distance_scalar mulrDl; apply: lerD.
- apply: ler_wpM2l; first exact hx.
  rewrite lef_pV2 ?inE //.
  by rewrite addrA lerDl.
- apply: ler_wpM2l; first exact hy.
  rewrite lef_pV2 ?inE //.
  by rewrite (addrC x y) addrA lerDl.
Qed.
