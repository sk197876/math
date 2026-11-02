(** Federer (1969), 3.2.7, p. 246:
    elementary laws of the auxiliary signed square root.
    Use only its opaque half-line specification, not
    its private existence witness. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import SignedSquareRootUP SignedSquareRootSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Laws.
Variable R:realType.
Local Notation G:=(@SignedSquareRoot.value R).
Local Notation ht:=(@SignedSquareRoot.laws R).

(** Source for [signed_root_zero]: the centre value
    of the parameter used in the third example of
    Federer 3.2.7, p. 246. *)
Lemma signed_root_zero:G 0= 0.
Proof. by rewrite (signed_square_root_nonnegative ht (lexx 0)) sqrtr0. Qed.

(** Source for [signed_root_sign_bounds]: the signed
    square root has the sign of its argument,
    supporting Federer 3.2.7, p. 246. *)
Lemma signed_root_sign_bounds x:
  (0<=x -> 0<=G x) /\ (x<= 0 -> G x<= 0).
Proof.
split=>hx.
- by rewrite (signed_square_root_nonnegative ht hx) sqrtr_ge0.
- by rewrite (signed_square_root_nonpositive ht hx) oppr_le0 sqrtr_ge0.
Qed.

(** Source for [signed_root_monotone]: finite variation
    of the auxiliary parameter in the third example of
    Federer 3.2.7, p. 246. The global
    monotonicity is derived from the scalar root order. *)
Lemma signed_root_monotone x y:x<=y -> G x<=G y.
Proof.
move=>hxy; case:(lerP 0 x)=>hx.
- have hy:0<=y:=le_trans hx hxy.
  rewrite (signed_square_root_nonnegative ht hx) (signed_square_root_nonnegative ht hy).
  exact:ler_wsqrtr hxy.
- case:(lerP 0 y)=>hy.
  + exact (le_trans ((signed_root_sign_bounds x).2 (ltW hx)) ((signed_root_sign_bounds y).1 hy)).
  + rewrite (signed_square_root_nonpositive ht (ltW hx))
      (signed_square_root_nonpositive ht (ltW hy)) lerN2.
    apply:ler_wsqrtr; by rewrite lerN2.
Qed.

(** Source for [signed_root_absolute_value]: the
    parameter has norm sqrt(|x|), supporting the
    oscillatory factorization in Federer 3.2.7, p. 246. *)
Lemma signed_root_absolute_value x:`|G x|=Num.sqrt `|x|.
Proof.
case:(lerP 0 x)=>hx.
- by rewrite (signed_square_root_nonnegative ht hx) (ger0_norm (sqrtr_ge0 x)) (ger0_norm hx).
- by rewrite (signed_square_root_nonpositive ht (ltW hx)) normrN
    (ger0_norm (sqrtr_ge0 (-x))) (ler0_norm (ltW hx)).
Qed.

(** Source for [signed_root_square]: the squared
    parameter is |x| in the third example of
    Federer 3.2.7, p. 246. *)
Lemma signed_root_square x:(G x)^+2=`|x|.
Proof.
case:(lerP 0 x)=>hx.
- by rewrite (signed_square_root_nonnegative ht hx) (sqr_sqrtr hx) (ger0_norm hx).
- have hn:0<= -x by rewrite oppr_ge0; exact:ltW hx.
  rewrite (signed_square_root_nonpositive ht (ltW hx)) exprNn /=
    (sqr_sqrtr hn) (ler0_norm (ltW hx)).
  by rewrite expr2 mulrNN !mul1r.
Qed.

(** Source for [signed_root_odd]: reflection of the
    square-root parameter, supporting the negative half-line
    of the third example in Federer 3.2.7, p. 246. *)
Lemma signed_root_odd x:G (-x)= -G x.
Proof.
case:(lerP 0 x)=>hx.
- have hn: -x<= 0 by rewrite oppr_le0.
  by rewrite (signed_square_root_nonpositive ht hn) (signed_square_root_nonnegative ht hx) opprK.
- have hn:0<= -x by rewrite oppr_ge0; exact:ltW hx.
  by rewrite (signed_square_root_nonnegative ht hn) (signed_square_root_nonpositive ht (ltW hx)) opprK.
Qed.
End Laws.
