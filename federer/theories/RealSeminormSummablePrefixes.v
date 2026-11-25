(** Federer (1969), 4.1.18, p. 376: summable
    bounds for the smooth coefficient fields make their
    finite prefixes Cauchy in the original L1 seminorm.
    Reuse the exact numerical tails of 2.1.1(13),
    p. 53, and the seminorm laws of 1.10.5,
    pp. 47–48. No positive definiteness is needed. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP NonnegativeSum NonnegativeRealSeriesTails.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Prefixes.
Variable R:realType.
Variable V:lmodType R.
Variable N:V->R.
Hypothesis hN:is_real_seminorm N.
Variable u:nat->V.
Variable a:nat->R.
Hypothesis ha:forall i,0<=a i.
Hypothesis hFinite:(nonnegative_sum setT (fun i=>(a i)%:E)< +oo)%E.
Hypothesis hBound:forall i,N (u i)<=a i.
Local Notation S:=(fun k=>\sum_(i<k) u i).
Local Notation t:=(nonnegative_real_series_tail a).

(** Source for [real_seminorm_prefix_tail_bound]: the
    exact numerical tail bounds every finite tail of
    the coefficient series in Federer 4.1.18, p. 376. *)
Lemma real_seminorm_prefix_tail_bound (i k:nat):
  N (S ((i+k)%N)-S i)<=t i-t ((i+k)%N).
Proof.
elim:k=>[|k ih].
- by rewrite addn0 subrr (real_seminorm_zero hN) subrr.
- rewrite addnS big_ord_recr /= addrAC.
  apply:(le_trans (real_seminorm_triangle hN _ _) _).
  apply:(le_trans (lerD ih (hBound ((i+k)%N))) _).
  rewrite -(@nonnegative_real_series_tail_step R a ha hFinite ((i+k)%N)).
  by rewrite addrA subrK.
Qed.

(** Source for [real_seminorm_prefix_cauchy]: the
    finite prefixes of a series with summable seminorm
    bounds are Cauchy, supporting the original compact
    L1 sum fields in Federer 4.1.18, p. 376. *)
Theorem real_seminorm_prefix_cauchy:
  forall epsilon:R,0<epsilon->exists L,forall i j,
    (L<=i)%N->(L<=j)%N->N (S i-S j)<epsilon.
Proof.
move=>epsilon hEpsilon.
have[L hL]:=@nonnegative_real_series_tail_small R a ha hFinite epsilon hEpsilon.
exists L=>i j hI hJ.
have hOrdered (p q:nat) (hP:(L<=p)%N) (hQ:(L<=q)%N) (hQP:(q<=p)%N):
    N (S p-S q)<epsilon.
  have hTail:=real_seminorm_prefix_tail_bound q (p-q)%N.
  rewrite subnKC // in hTail.
  apply:(le_lt_trans hTail _).
  apply:(le_lt_trans _ (hL q hQ)).
  rewrite lerBlDr lerDl;exact:(@nonnegative_real_series_tail_nonnegative R a hFinite p).
case:(leqP j i)=>hOrder.
- exact:(hOrdered i j hI hJ hOrder).
- rewrite (real_seminorm_subtract hN).
  exact:(hOrdered j i hJ hI (ltnW hOrder)).
Qed.
End Prefixes.
