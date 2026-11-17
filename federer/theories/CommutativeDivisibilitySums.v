(** Federer (1969), 3.4.7, p. 325: finite divisibility
    arguments supporting the primitive-product step of Gauss's lemma. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeFactorizationUP CommutativeDivisibility.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [commutative_divides_finite_sum]: divisibility
    is preserved by a finite sum, supporting the
    coefficient argument in 3.4.7, p. 325. *)
Lemma commutative_divides_finite_sum (A:comNzRingType) (I:eqType)
    (r:seq I) (P:pred I) (f:I->A) p:
  (forall i,i\in r ->P i ->commutative_divides p (f i)) ->
  commutative_divides p (\sum_(i<-r|P i) f i).
Proof.
move=>h;rewrite big_seq_cond;elim/big_rec:_=>[|i x hi hx];first exact:commutative_divides_zero.
apply:commutative_divides_add;last exact:hx.
move/andP:hi=>[hir hPi];exact:h i hir hPi.
Qed.

(** Source for [commutative_divides_sum_remainder]: subtracting
    a divisible summand leaves a divisible remainder,
    supporting 3.4.7, p. 325. *)
Lemma commutative_divides_sum_remainder (A:comNzRingType) (p x y:A):
  commutative_divides p (x+y) ->commutative_divides p y ->commutative_divides p x.
Proof.
move=>hSum hY.
have h:=commutative_divides_add hSum (commutative_divides_negate hY).
by rewrite -addrA addrN addr0 in h.
Qed.

(** Source for [commutative_prime_product_not_divisible]: a
    prime cannot divide a product of two elements
    it does not divide, supporting 3.4.7, p. 325. *)
Lemma commutative_prime_product_not_divisible (A:comNzRingType) (p x y:A):
  is_commutative_prime_element p ->
  ~commutative_divides p x ->~commutative_divides p y ->~commutative_divides p (x*y).
Proof.
move=>[_ [_ hPrime]] hx hy hProduct.
case:(hPrime x y hProduct)=>h;[exact:hx h|exact:hy h].
Qed.
