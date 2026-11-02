(** Federer (1969), 2.1.1, pp. 51-52: partial extended-real arithmetic and
    positive and negative parts. We reuse extended scalars as background,
    but expose undefined operations as None: the library's total arithmetic
    is not Federer's partial arithmetic. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [extended_add]: Federer 2.1.1, p. 51, opening paragraph;
    definition of addition excluding opposite infinities. *)
Definition extended_add (R : realDomainType) (x y : \bar R) :=
  if adde_def x y then Some (x + y) else None.

(** Source for [extended_subtract]: Federer 2.1.1, p. 51,
    opening paragraph; subtraction is undefined for equal infinities. *)
Definition extended_subtract (R : realDomainType) (x y : \bar R) :=
  extended_add x (- y).

(** Source for [extended_multiply]: Federer 2.1.1, p. 51, opening paragraph;
    the ordinary partial product excludes a zero factor paired with either
    infinity. *)
Definition extended_multiply (R : realDomainType) (x y : \bar R) :=
  if mule_def x y then Some (x * y) else None.

(** Source for [extended_zero_product]: Federer 2.1.1, p. 51,
    second paragraph, and p. 53 (11); the explicitly distinguished
    convention assigns zero to zero times infinity. *)
Definition extended_zero_product (R : realDomainType) (x y : \bar R) := x * y.

(** Source for [extended_add_defined]: Federer 2.1.1, p. 51,
    supporting characterization of the domain of partial addition. *)
Lemma extended_add_defined (R : realDomainType) (x y : \bar R) :
  (exists z, extended_add x y = Some z) <-> adde_def x y.
Proof.
rewrite /extended_add; case: (adde_def x y).
- split=> // _; by exists (x + y).
- by split=> [[z] //|].
Qed.

(** Source for [extended_add_opposite_infinities]: Federer
    2.1.1, p. 51, example: infinity minus infinity is undefined. *)
Lemma extended_add_opposite_infinities (R : realDomainType) :
  extended_add (+oo : \bar R) (-oo) = None.
Proof. by []. Qed.

(** Source for [extended_multiply_zero_infinity]: Federer
    2.1.1, p. 51, example: zero times infinity is undefined. *)
Lemma extended_multiply_zero_infinity (R : realDomainType) :
  extended_multiply (0 : \bar R) (+oo) = None.
Proof. by rewrite /extended_multiply /mule_def /= eqxx. Qed.

(** Source for [extended_zero_product_zero]: Federer 2.1.1,
    p. 51, special convention, valid also for negative infinity. *)
Lemma extended_zero_product_zero (R : realDomainType) (x : \bar R) :
  extended_zero_product 0 x = 0.
Proof. exact: mul0e. Qed.

(** Source for [extended_positive_part]: Federer 2.1.1, p. 52, first
    display, paraphrase: the positive part is the maximum with zero. *)
Definition extended_positive_part (R : realDomainType) (x : \bar R) :=
  Order.max x 0.

(** Source for [extended_negative_part]: Federer 2.1.1, p. 52,
    first display, paraphrase: the negative part is minus the minimum
    with zero, equivalently the positive part of the negative. *)
Definition extended_negative_part (R : realDomainType) (x : \bar R) :=
  extended_positive_part (-x).

(** Source for [extended_sign]: Federer 2.1.1, p. 51, final
    sentence; sign takes the real values minus one, zero or one. *)
Definition extended_sign (R : realDomainType) (x : \bar R) : R :=
  if 0 < x then 1%R else if x < 0 then (-1)%R else 0%R.

(** Source for [extended_positive_part_nonnegative]: Federer
    2.1.1, p. 52, sentence following the first display; direct claim. *)
Lemma extended_positive_part_nonnegative (R : realDomainType) (x : \bar R) :
  0 <= extended_positive_part x.
Proof. by rewrite /extended_positive_part le_max lexx orbT. Qed.

(** Source for [extended_negative_part_nonnegative]: Federer
    2.1.1, p. 52, sentence following the first display; direct claim. *)
Lemma extended_negative_part_nonnegative (R : realDomainType) (x : \bar R) :
  0 <= extended_negative_part x.
Proof. exact: extended_positive_part_nonnegative. Qed.

(** Source for [extended_positive_negative_parts]: Federer 2.1.1, p. 52,
    second display; the difference of the parts is defined and equals the
    original value, including both infinities. *)
Lemma extended_positive_negative_parts (R : realDomainType) (x : \bar R) :
  extended_subtract (extended_positive_part x) (extended_negative_part x) = Some x.
Proof.
rewrite /extended_subtract /extended_negative_part /extended_positive_part.
have [hx|hx] := leP 0 x.
- rewrite (max_r _); last by rewrite oppe_le0.
  by rewrite oppe0 /extended_add fin_num_adde_defl // adde0.
- have hnx : 0 <= -x by rewrite oppe_ge0; exact: ltW hx.
  rewrite (max_l hnx) oppeK /extended_add.
  by rewrite fin_num_adde_defr // add0e.
Qed.

(** Source for [extended_absolute_parts]: Federer 2.1.1, p. 52, second
    display; absolute value is the sum of the parts. *)
Lemma extended_absolute_parts (R : realDomainType) (x : \bar R) :
  `|x| = extended_positive_part x + extended_negative_part x.
Proof.
rewrite /extended_negative_part /extended_positive_part.
have [hx|hx] := leP 0 x.
- rewrite (max_r _); last by rewrite oppe_le0.
  by rewrite adde0 gee0_abs.
- have hnx : 0 <= -x by rewrite oppe_ge0; exact: ltW hx.
  by rewrite (max_l hnx) add0e lee0_abs // ltW.
Qed.
