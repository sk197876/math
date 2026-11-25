(** Federer (1969), 3.1.24, p. 239: identifying
    the order-zero series limit with the given function.
    The supporting fact is uniqueness of norm limits. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_sequence_limit_unique]: supporting
    f=sum_m p_m in Federer 3.1.24, p. 239.
    A sequence cannot have two different limits in a
    normed space. The proof uses only the triangle
    inequality and definiteness of the supplied norm. *)
Lemma norm_sequence_limit_unique (R:realType) (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (u:nat->Y) y z :
  (forall eps:R,0<eps -> exists n:nat,forall N,(n<=N)%N -> NY (u N-y)<eps) ->
  (forall eps:R,0<eps -> exists n:nat,forall N,(n<=N)%N -> NY (u N-z)<eps) -> y= z.
Proof.
move=>hy hz.
have hle:NY (y-z)<=0.
  apply/ler_addgt0Pr=>eps he.
  have he2:0<eps/2 by lra.
  have [k hk]:=hy (eps/2) he2.
  have [l hl]:=hz (eps/2) he2.
  have hkN:(k<=maxn k l)%N:=leq_maxl _ _.
  have hlN:(l<=maxn k l)%N:=leq_maxr _ _.
  have h1:=hk (maxn k l) hkN.
  have h2:=hl (maxn k l) hlN.
  rewrite (real_seminorm_subtract hNY.1) in h1.
  have ht:=real_seminorm_triangle hNY.1 (y-u (maxn k l)) (u (maxn k l)-z).
  rewrite addrA subrK in ht.
  have hh:=le_lt_trans ht (ltrD h1 h2).
  have heq:eps/2+eps/2= eps by lra.
  rewrite heq in hh.
  rewrite add0r; exact: ltW hh.
have hzero:NY (y-z)= 0.
  apply/eqP; rewrite eq_le hle; exact: real_seminorm_nonnegative hNY.1 _.
exact: subr0_eq (hNY.2 _ hzero).
Qed.
