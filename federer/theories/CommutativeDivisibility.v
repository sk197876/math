(** Federer (1969), 3.4.7, p. 325: elementary
    divisibility in the coefficient and polynomial rings
    used by the Gauss argument. These supporting laws
    use the independent existential divisibility definition. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeFactorizationUP CommutativeUnitLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [commutative_divides_reflexive]: each
    element divides itself, supporting 3.4.7, p. 325. *)
Lemma commutative_divides_reflexive (A:comNzRingType) (x:A):commutative_divides x x.
Proof. exists 1;by rewrite mul1r. Qed.

(** Source for [commutative_divides_zero]: each element
    divides zero, supporting 3.4.7, p. 325. *)
Lemma commutative_divides_zero (A:comNzRingType) (x:A):commutative_divides x 0.
Proof. exists 0;by rewrite mul0r. Qed.

(** Source for [commutative_divides_transitive]: divisibility
    is transitive, supporting 3.4.7, p. 325. *)
Lemma commutative_divides_transitive (A:comNzRingType) (x y z:A):
  commutative_divides x y ->commutative_divides y z ->commutative_divides x z.
Proof.
move=>[a hy] [b hz];exists (b*a);by rewrite hz hy mulrA.
Qed.

(** Source for [commutative_divides_add]: divisibility
    is closed under sums, supporting 3.4.7, p. 325. *)
Lemma commutative_divides_add (A:comNzRingType) (p x y:A):
  commutative_divides p x ->commutative_divides p y ->commutative_divides p (x+y).
Proof. move=>[a ->] [b ->];exists (a+b);by rewrite mulrDl. Qed.

(** Source for [commutative_divides_negate]: divisibility
    is closed under negation, supporting 3.4.7, p. 325. *)
Lemma commutative_divides_negate (A:comNzRingType) (p x:A):
  commutative_divides p x ->commutative_divides p (-x).
Proof. move=>[a ->];exists (-a);by rewrite mulNr. Qed.

(** Source for [commutative_divides_multiply]: multiplying
    a divisible element preserves divisibility, supporting
    3.4.7, p. 325. *)
Lemma commutative_divides_multiply (A:comNzRingType) (p x y:A):
  commutative_divides p y ->commutative_divides p (x*y).
Proof. move=>[a ->];exists (x*a);by rewrite mulrA. Qed.

(** Source for [commutative_divides_one_unit]: a divisor
    of one is a unit, supporting the Gauss
    argument in 3.4.7, p. 325. *)
Lemma commutative_divides_one_unit (A:comNzRingType) (p:A):
  commutative_divides p 1 <->is_commutative_unit p.
Proof.
split=>[[a h]|[a h]];exists a;exact:esym h.
Qed.

(** Source for [commutative_unit_divides_everything]: units
    divide every element, supporting 3.4.7, p. 325. *)
Lemma commutative_unit_divides_everything (A:comNzRingType) (p x:A):
  is_commutative_unit p ->commutative_divides p x.
Proof.
move=>[a ha];exists (x*a);by rewrite -mulrA ha mulr1.
Qed.

(** Source for [commutative_unit_divisor_unit]: a divisor
    of a unit is itself a unit, supporting
    the factorization argument in 3.4.7, p. 325. *)
Lemma commutative_unit_divisor_unit (A:comNzRingType) (p x:A):
  is_commutative_unit x ->commutative_divides p x ->is_commutative_unit p.
Proof.
move=>hUnit [a h];rewrite h in hUnit.
exact:((@commutative_product_unit A a p).1 hUnit).2.
Qed.
