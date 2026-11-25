(** Federer (1969), 3.1.24, p. 240: the scalar
    derivatives of the positive square root used by the
    quadratic inverse majorant. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [square_root_falling_coefficient]: supporting
    the square root in Federer 3.1.24, p. 240.
    The mth derivative coefficient contains the falling
    product (1/2)(1/2-1)...(1/2-m+1); the empty product is one. *)
Definition square_root_falling_coefficient (R:realType) m:R :=
  \prod_(j<m) (2^-1-j%:R).
Arguments square_root_falling_coefficient {R} m.

(** Source for [square_root_falling_zero]: the empty coefficient
    equals one, supporting the order-zero term of the scalar
    quadratic inverse calculation, Federer 3.1.24, p. 240. *)
Lemma square_root_falling_zero (R:realType) :
  @square_root_falling_coefficient R 0= 1.
Proof. by rewrite /square_root_falling_coefficient big_ord0. Qed.

(** Source for [square_root_falling_successor]: adjoining the
    next factor gives the derivative recurrence, supporting
    Federer 3.1.24, p. 240. *)
Lemma square_root_falling_successor (R:realType) m :
  @square_root_falling_coefficient R m.+1=
    square_root_falling_coefficient m*(2^-1-m%:R).
Proof. by rewrite /square_root_falling_coefficient big_ord_recr. Qed.

(** Source for [square_root_falling_factorial_bound]: the
    absolute falling coefficient is bounded by m!, sufficient
    for the local analytic bound on the positive square root
    used in Federer 3.1.24, p. 240. *)
Lemma square_root_falling_factorial_bound (R:realType) m :
  `|@square_root_falling_coefficient R m|<=(m`!)%:R.
Proof.
elim:m=>[|m ih].
- by rewrite square_root_falling_zero fact0 normr1.
- rewrite square_root_falling_successor normrM factS natrM.
  have hb:`|(2:R)^-1-m%:R|<=m.+1%:R.
    have hn:0<=(m%:R:R):=ler0n _ _.
    rewrite -addn1 natrD natr1 ler_norml; apply/andP; split; lra.
  apply: le_trans (ler_wpM2r (normr_ge0 _) ih) _.
  rewrite mulrC; exact (ler_wpM2r (ler0n R (m`!)) hb).
Qed.
