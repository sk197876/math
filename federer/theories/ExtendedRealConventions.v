(** Federer (1969), 2.1.1, pp. 51-52: extended-real conventions, sign and
    negative part. editions: ExtendedRealPartial.v. Scalar types and their
    arithmetic are background; the public partial operations retain the
    book's domains explicitly. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealPartial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [extended_divide]: Federer 2.1.1, p. 51, opening paragraph;
    division excludes zero denominators and pairs of infinities. *)
Definition extended_divide (R : realType) (x y : \bar R) :=
  if (y != 0) && ((x \is a fin_num) || (y \is a fin_num))
  then Some (x/y) else None.

(** Source for [extended_divide_zero]: Federer 2.1.1,
    p. 51, opening paragraph; division by zero has no value under
    the order-topology extension convention. *)
Lemma extended_divide_zero (R : realType) (x : \bar R) :
  extended_divide x 0 = None.
Proof. by rewrite /extended_divide eqxx. Qed.

(** Source for [extended_divide_infinities]: Federer 2.1.1,
    p. 51, opening paragraph; infinity divided by infinity is undefined. *)
Lemma extended_divide_infinities (R : realType) :
  extended_divide (+oo : \bar R) (+oo) = None.
Proof. by []. Qed.

(** Source for [extended_negative_part_min]: Federer 2.1.1,
    p. 52, first display; the chosen negative part equals minus
    the minimum of the value and zero, precisely as printed. *)
Lemma extended_negative_part_min (R : realType) (x : \bar R) :
  extended_negative_part x = - Order.min x 0.
Proof. by rewrite oppe_min oppe0. Qed.

(** Source for [extended_sign_zero]: Federer 2.1.1, p. 51,
    last sentence; the sign of zero is zero. *)
Lemma extended_sign_zero (R : realType) : extended_sign (0 : \bar R) = 0%R.
Proof. by rewrite /extended_sign ltxx. Qed.

(** Source for [extended_sign_positive]: Federer 2.1.1,
    p. 51, last sentence; the sign of a positive value is one. *)
Lemma extended_sign_positive (R : realType) (x : \bar R) :
  0 < x -> extended_sign x = 1%R.
Proof. by move=> hx; rewrite /extended_sign hx. Qed.

(** Source for [extended_sign_negative]: Federer 2.1.1,
    p. 51, last sentence; the sign of a negative value is minus one. *)
Lemma extended_sign_negative (R : realType) (x : \bar R) :
  x < 0 -> extended_sign x = (-1)%R.
Proof.
by move=> hx; rewrite /extended_sign hx ltNge (ltW hx).
Qed.
