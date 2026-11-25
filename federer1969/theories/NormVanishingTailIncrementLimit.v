(** Federer (1969), 4.1.12, pp. 368–369: the
    two original current series have summable mass
    tails. This supporting completeness argument reuses
    the preceding telescoping norm bound, Cauchy
    completeness and closed norm-limit estimate. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP NormGeometricIncrementLimit
  NormSequenceConvergence NormSequenceClosedBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_vanishing_tail_increments_converge]:
    partial sums whose norm increments are bounded
    by losses of a vanishing nonnegative tail
    budget converge in the supplied complete normed
    space. Their limit retains that exact tail bound,
    supporting the two series in Federer 4.1.12,
    pp. 368–369. No series object is chosen globally. *)
Theorem norm_vanishing_tail_increments_converge (R:realType) (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY)
    (hComplete:is_complete_metric_space (real_norm_metric_space hNY))
    (u:nat->Y) (t:nat->R):
  (forall n,0<=t n)->
  (forall n,NY (u n.+1-u n)<=t n-t n.+1)->
  (forall epsilon:R,0<epsilon->exists n,t n<epsilon)->
  exists z:Y,
    ((fun n=>(u n:real_norm_metric_space hNY)) @ \oo -->
      (z:real_norm_metric_space hNY)) /\
    forall n,NY (z-u n)<=t n.
Proof.
move=>hT hIncrement hSmall.
have hBound:=@norm_increment_tail_bound R Y NY hNY u t hT hIncrement.
have hCauchy:cauchy ((fun n=>(u n:real_norm_metric_space hNY)) @ \oo).
  apply:cauchy_exP=>epsilon hEpsilon.
  have [k hk]:=hSmall epsilon hEpsilon.
  exists (u k:real_norm_metric_space hNY);exists k=>// n hKN.
  rewrite ballEmdist /=.
  change (is_true (NY (u k-u n)<epsilon)).
  rewrite (real_seminorm_subtract hNY.1).
  exact:le_lt_trans (hBound k n hKN) hk.
have hProperNat:ProperFilter (\oo:set_system nat) by typeclasses eauto.
have hProper:ProperFilter ((fun n=>(u n:real_norm_metric_space hNY)) @ \oo):=
  @fmap_proper_filter nat (real_norm_metric_space hNY) u \oo hProperNat.
have [z hZ]:=@hComplete _ hProper hCauchy.
exists z;split;first exact:hZ.
move=>n.
have hEpsilon:=(@norm_sequence_convergence_epsilon R Y NY hNY u z).1 hZ.
have hConstant:forall epsilon:R,0<epsilon->exists k:nat,forall N,(k<=N)%N->
    NY (u n-u n)<epsilon.
  move=>eta hEta;exists 0%N=>N _.
  by rewrite subrr (real_seminorm_zero hNY.1).
have hDifference:=@norm_sequence_limit_difference R Y NY hNY.1 u (fun _=>u n) z (u n)
  hEpsilon hConstant.
exact:(@norm_sequence_limit_closed_bound R Y NY hNY.1 (fun N=>u N-u n) (z-u n) (t n) n
  hDifference (hBound n)).
Qed.
