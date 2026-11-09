(** Federer (1969), 3.4.6(1), pp. 321–322:
    translating a finite polynomial in the distinguished
    coordinate preserves its degree bound. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_finite_shift_expansion]: the
    finite remainder remains a polynomial of degree below k
    on every translated distinguished line, supporting
    3.4.6(1), pp. 321–322. Only the finite binomial
    theorem and finite exchange of sums are used. *)
Theorem weierstrass_finite_shift_expansion (R:realType) k (a t:R) (d:nat->R):
  (\sum_(i<k) (a+t)^+i*d i)=
    \sum_(n<k) t^+n*(\sum_(i<k | (n<=i)%N) ('C(i,n))%:R*a^+(i-n)*d i).
Proof.
have hExpand (i:'I_k):((a+t)^+i*d i)=
    \sum_(n<k) if (n<=i)%N then t^+n*(('C(i,n))%:R*a^+(i-n)*d i) else 0.
  have hi:(i.+1<=k)%N:=ltn_ord i.
  rewrite exprDn mulr_suml
    (big_ord_widen k (fun n=>a^+(i-n)*t^+n*+('C(i,n))*d i) hi) big_mkcond.
  apply:eq_bigr=>n _;rewrite ltnS.
  case:(n<=i)%N=>//.
  rewrite -mulr_natl;ring.
under eq_bigr do rewrite hExpand.
rewrite exchange_big;apply:eq_bigr=>n _.
have hCond:(\sum_(i<k | (n<=i)%N) ('C(i,n))%:R*a^+(i-n)*d i)=
    \sum_(i<k) if (n<=i)%N then ('C(i,n))%:R*a^+(i-n)*d i else 0.
  by rewrite big_mkcond.
rewrite hCond mulr_sumr.
apply:eq_bigr=>i _;by case:(n<=i)%N;rewrite ?mulr0.
Qed.
