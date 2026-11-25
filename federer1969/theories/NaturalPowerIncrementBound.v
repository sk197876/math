(** Federer (1969), 3.2.38, p. 275: the inflation factor
    (1+m/v)^(n-j) contributes a controlled first-order error. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [nonnegative_power_linear_increment_bound]: supporting
    the uniform xi/v error in Federer 3.2.38, p. 275. The
    finite geometric-sum identity bounds (1+s)^k-1 by s times
    a constant depending only on an upper bound for s and k.
    The zero exponent is retained and gives zero error. *)
Lemma nonnegative_power_linear_increment_bound (R:realType) (M s:R) k:
  0<=s ->s<=M ->
  (1+s)^+k<=1+s*(\sum_(i<k) (1+M)^+i).
Proof.
move=>hs hsM.
have hBase:0<=1+s by exact:addr_ge0 ler01 hs.
have hOrder:1+s<=1+M by rewrite lerD2l.
have hPower j:(1+s)^+j<=(1+M)^+j.
  elim:j=>[|j hj]; first by rewrite !expr0.
  rewrite !exprS; exact:ler_pM hBase (exprn_ge0 j hBase) hOrder hj.
have hSum:(\sum_(i<k) (1+s)^+i)<=\sum_(i<k) (1+M)^+i.
  apply:ler_sum=>i _; exact:hPower.
have hDifference:(1+s)^+k-1=s*(\sum_(i<k) (1+s)^+i).
  by rewrite subrX1 addrAC subrr add0r.
have hBound:=ler_wpM2l hs hSum.
rewrite -hDifference in hBound.
lra.
Qed.
