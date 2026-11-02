(** Federer (1969), 3.1.24, pp. 238–239:
    a uniform tail bound for geometrically dominated series. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology ring.
From Federer Require Import RealNormUP NormMetric NormGeometricIncrementLimit
  NormSequenceConvergence NormSequenceClosedBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_geometric_increments_limit_error]: supporting
    uniform convergence of the derivative series in Federer
    3.1.24, pp. 238–239. If consecutive partial sums
    differ by at most c^n a, then every partial sum
    is within c^n a/(1-c) of the limit. The
    proof passes the finite telescoping bound to the norm
    limit; the coefficient a may be zero. *)
Lemma norm_geometric_increments_limit_error (R:realType) (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (u:nat->Y) z c a :
  0<c<1 -> 0<=a ->
  (forall n,NY (u n.+1-u n)<=c^+n*a) ->
  ((fun n=>(u n:real_norm_metric_space hNY)) @ \oo -->
    (z:real_norm_metric_space hNY)) ->
  forall n,NY (z-u n)<=c^+n*a/(1-c).
Proof.
move=>hc ha hs hz n.
have hc0:0<c:=(andP hc).1.
have hc1:c<1:=(andP hc).2.
have hd:0<1-c by rewrite subr_gt0.
have hd0:1-c!=0:=lt0r_neq0 hd.
pose t:=fun k=>c^+k*a/(1-c).
have ht k:0<=t k.
  apply: divr_ge0; last exact: ltW hd.
  exact (mulr_ge0 (exprn_ge0 k (ltW hc0)) ha).
have hstep k:t k-t k.+1= c^+k*a.
  rewrite /t exprS -mulrBl.
  have heq:c^+k*a-c*c^+k*a= (c^+k*a)*(1-c) by ring.
  by rewrite heq mulfK.
have hfinite k:NY (u k.+1-u k)<=t k-t k.+1 by rewrite hstep; exact: hs.
have hb:=@norm_increment_tail_bound R Y NY hNY u t ht hfinite.
have heps:=(@norm_sequence_convergence_epsilon R Y NY hNY u z).1 hz.
have hconst:forall eps:R,0<eps -> exists k:nat,forall N,(k<=N)%N ->
    NY (u n-u n)<eps.
  by move=>eps he; exists 0%N=>N _; rewrite subrr (real_seminorm_zero hNY.1).
have hconv:=@norm_sequence_limit_difference R Y NY hNY.1 u (fun _=>u n) z (u n) heps hconst.
exact (@norm_sequence_limit_closed_bound R Y NY hNY.1 (fun N=>u N-u n)
  (z-u n) (t n) n hconv (hb n)).
Qed.
