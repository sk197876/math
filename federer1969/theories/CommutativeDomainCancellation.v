(** Federer (1969), 3.4.7, p. 325: cancellation
    in the coefficient domain used by the Gauss
    argument. The zero-divisor law is separate from
    the factorization property. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeDomainUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [commutative_domain_cancel_left]: a
    nonzero coefficient cancels from a product equation,
    supporting 3.4.7, p. 325. *)
Lemma commutative_domain_cancel_left (A:comNzRingType)
    (hDomain:is_commutative_integral_domain A) (a x y:A):
  a<>0 ->a*x = a*y ->x = y.
Proof.
move=>ha hEqual.
have hProduct:a*(x-y) = 0 by rewrite mulrBr hEqual subrr.
case:(hDomain a (x-y) hProduct)=>[hZero|hZero];first by exfalso;exact:ha hZero.
exact:subr0_eq hZero.
Qed.

(** Source for [commutative_domain_product_nonzero]: a
    product of nonzero coefficients is nonzero, supporting
    the Gauss argument in 3.4.7, p. 325. *)
Lemma commutative_domain_product_nonzero (A:comNzRingType)
    (hDomain:is_commutative_integral_domain A) (x y:A):
  x<>0 ->y<>0 ->x*y<>0.
Proof.
move=>hx hy hProduct;case:(hDomain x y hProduct)=>h;[exact:hx h|exact:hy h].
Qed.
