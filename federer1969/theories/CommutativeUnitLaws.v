(** Federer (1969), 3.4.7, p. 325: units
    and their products in the preparation and factorization
    argument. These supporting algebraic laws use the independent
    inverse specification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativeFactorizationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [commutative_one_unit]: the constant
    one is a unit, supporting 3.4.7, p. 325. *)
Lemma commutative_one_unit (A:comNzRingType):is_commutative_unit (1:A).
Proof. exists 1;exact:mul1r. Qed.

(** Source for [commutative_zero_not_unit]: zero is
    not a unit in the nonzero ring used for
    3.4.7, p. 325. *)
Lemma commutative_zero_not_unit (A:comNzRingType):~is_commutative_unit (0:A).
Proof.
move=>[y h];rewrite mulr0 in h.
have h01:(0:A)!=1 by rewrite eq_sym oner_eq0.
by rewrite h eqxx in h01.
Qed.

(** Source for [commutative_unit_nonzero]: every unit
    is nonzero, supporting 3.4.7, p. 325. *)
Lemma commutative_unit_nonzero (A:comNzRingType) (x:A):
  is_commutative_unit x ->x<>0.
Proof. move=>h hx;rewrite hx in h;exact:commutative_zero_not_unit h. Qed.

(** Source for [commutative_product_unit]: a product
    is a unit exactly when both its factors are
    units, supporting 3.4.7, p. 325. *)
Lemma commutative_product_unit (A:comNzRingType) (x y:A):
  is_commutative_unit (x*y) <->is_commutative_unit x /\is_commutative_unit y.
Proof.
split.
- move=>[z hz];split.
  + exists (z*y);rewrite mulrAC -mulrA;exact:hz.
  + exists (z*x);rewrite -mulrA;exact:hz.
- move=>[[u hu] [v hv]];exists (u*v).
  by rewrite mulrACA hu hv mul1r.
Qed.

(** Source for [commutative_inverse_unit]: an inverse
    of a unit is itself a unit, supporting the
    preparation normalization in 3.4.7, p. 325. *)
Lemma commutative_inverse_unit (A:comNzRingType) (x y:A):
  y*x = 1 ->is_commutative_unit y.
Proof. move=>h;exists x;by rewrite mulrC. Qed.
