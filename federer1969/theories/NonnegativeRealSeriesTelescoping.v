(** Federer (1969), 2.1.1(13), p. 53,
    used for the explicit series in
    4.1.12, p. 369: a nonnegative
    series bounded by successive differences of
    nonnegative remainders has finite sum.
    Reuse the original finite-prefix and supremum laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal lra.
From Federer Require Import NonnegativeSum NonnegativeSeriesParity CosetLoneIntegralExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [nonnegative_real_series_telescoping_bound]:
    if a_k<=t_k-t_(k+1), a_k>=0 and
    t_k>=0, every original numerical sum
    of the a_k is at most t_0.
    This supports the reciprocal-power series in
    Federer 4.1.12, p. 369, by
    the earlier numerical sum laws. *)
Theorem nonnegative_real_series_telescoping_bound (R:realType) (a t:nat->R):
  (forall k,0<=a k)->(forall k,0<=t k)->
  (forall k,a k<=t k-t k.+1)->
  (nonnegative_sum setT (fun k=>(a k)%:E)<=(t 0%N)%:E)%E.
Proof.
move=>ha ht hStep.
have hPrefix N: \sum_(k<N) a k<=t 0%N-t N.
  elim:N=>[|N ih];first by rewrite big_ord0 subrr.
  rewrite big_ord_recr /=;have h:=hStep N;lra.
apply:nonnegative_series_prefix_bound=>N.
rewrite (@nat_prefix_nonnegative_sum R a N ha) lee_fin.
have h:=hPrefix N;have h0:=ht N;lra.
Qed.
