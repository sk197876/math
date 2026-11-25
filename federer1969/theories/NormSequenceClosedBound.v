(** Federer (1969), 3.1.24, pp. 238–239:
    supporting closed norm bounds when passing to the limit
    of the polynomial partial sums and their differentials. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_sequence_limit_closed_bound]: supporting
    the termwise differentiation limit in Federer 3.1.24,
    pp. 238–239. A norm-convergent sequence whose sufficiently
    late terms are bounded by M has limit norm at most M. *)
Lemma norm_sequence_limit_closed_bound (R:realType) (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_seminorm NY) (u:nat->Y) z M n :
  (forall eps:R,0<eps -> exists k:nat,forall N,(k<=N)%N -> NY (u N-z)<eps) ->
  (forall N,(n<=N)%N -> NY (u N)<=M) -> NY z<=M.
Proof.
move=>hc hb; apply/ler_addgt0Pr=>eps he.
have [k hk]:=hc eps he.
have hn:(n<=maxn n k)%N:=leq_maxl _ _.
have hkn:(k<=maxn n k)%N:=leq_maxr _ _.
have hs:=hk (maxn n k) hkn.
rewrite (real_seminorm_subtract hNY) in hs.
have ht:=real_seminorm_triangle hNY (z-u (maxn n k)) (u (maxn n k)).
rewrite subrK in ht.
apply: ltW; apply: le_lt_trans ht _.
have hh:=ltr_leD hs (hb (maxn n k) hn).
by rewrite [M+eps]addrC; exact hh.
Qed.

(** Source for [norm_sequence_limit_difference]: supporting
    the same passage, Federer 3.1.24, pp. 238–239.
    Pointwise limits commute with subtraction in the supplied
    norm, proved by the triangle inequality. *)
Lemma norm_sequence_limit_difference (R:realType) (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_seminorm NY) (u v:nat->Y) y z :
  (forall eps:R,0<eps -> exists n:nat,forall N,(n<=N)%N -> NY (u N-y)<eps) ->
  (forall eps:R,0<eps -> exists n:nat,forall N,(n<=N)%N -> NY (v N-z)<eps) ->
  forall eps:R,0<eps -> exists n:nat,forall N,(n<=N)%N ->
    NY ((u N-v N)-(y-z))<eps.
Proof.
move=>hu hv eps he.
have he2:0<eps/2 by lra.
have [k hk]:=hu (eps/2) he2.
have [l hl]:=hv (eps/2) he2.
exists (maxn k l)=>N hN.
have hkN:(k<=N)%N:=leq_trans (leq_maxl _ _) hN.
have hlN:(l<=N)%N:=leq_trans (leq_maxr _ _) hN.
have heq:(u N-v N)-(y-z)= (u N-y)-(v N-z).
  rewrite !opprB (addrACA (u N) (-v N) z (-y))
    (addrACA (u N) (-y) z (-v N)).
  by rewrite [(-v N)+(-y)]addrC.
rewrite heq.
have ht:=real_seminorm_triangle hNY (u N-y) (-(v N-z)).
rewrite (real_seminorm_negate hNY) in ht.
have hh:=ltrD (hk N hkN) (hl N hlN).
have hhalf:eps/2+eps/2= eps by lra.
rewrite hhalf in hh.
exact (le_lt_trans ht hh).
Qed.
