(** Federer (1969), 3.4.7, p. 325: subring
    closure contains every finite original polynomial expression.
    Only the independent subring laws are used. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
From Federer Require Import CommutativeSubringUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [commutative_subring_power]: powers of an
    original member remain in the subring, supporting
    the polynomial subring in 3.4.7, p. 325. *)
Lemma commutative_subring_power (A:comNzRingType) (S:set A)
    (hS:is_commutative_subring S) (x:A) n:S x ->S (x^+n).
Proof.
move=>hx;elim:n=>[|n ih];first by rewrite expr0;exact:commutative_subring_one hS.
rewrite exprS;exact:(@commutative_subring_multiply A S hS x (x^+n) hx ih).
Qed.

(** Source for [commutative_subring_finite_sum]: a finite
    sum of original members remains in the subring,
    supporting the generated subring of 3.4.7, p. 325. *)
Lemma commutative_subring_finite_sum (A:comNzRingType) (S:set A)
    (hS:is_commutative_subring S) (I:eqType) (r:seq I) (P:pred I) (f:I->A):
  (forall i,i\in r ->P i ->S (f i)) ->S (\sum_(i<-r|P i) f i).
Proof.
move=>h;rewrite big_seq_cond;elim/big_rec:_=>[|i x hi hx];first exact:commutative_subring_zero hS.
apply:(@commutative_subring_add A S hS);last exact:hx.
move/andP:hi=>[hir hPi];exact:h i hir hPi.
Qed.
