(** Federer (1969), 3.1.24, pp. 238–239:
    the elementary sequence-limit adapter for the norm metrics
    used in the analytic series proof. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_sequence_convergence_epsilon]: supporting
    the Banach-space series limits in Federer 3.1.24,
    pp. 238–239. Convergence in the supplied norm metric
    is exactly the usual eventually-small norm of the error. *)
Lemma norm_sequence_convergence_epsilon (R:realType) (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (u:nat->Y) z :
  ((fun n=>(u n:real_norm_metric_space hNY)) @ \oo -->
    (z:real_norm_metric_space hNY)) <->
  forall eps:R,0<eps -> exists n:nat,forall N,(n<=N)%N -> NY (u N-z)<eps.
Proof.
split.
- move=>/cvg_ballP hc eps he.
  have [n _ hn]:=hc eps he.
  exists n=>N hN; have hh:=hn N hN.
  rewrite ballEmdist /= in hh.
  change (is_true (NY (z-u N)<eps)) in hh.
  by rewrite (real_seminorm_subtract hNY.1).
- move=>hc; apply/cvg_ballP=>eps he.
  have [n hn]:=hc eps he.
  exists n=>// N hN.
  rewrite ballEmdist /=.
  change (NY (z-u N)<eps).
  rewrite (real_seminorm_subtract hNY.1); exact: hn N hN.
Qed.
