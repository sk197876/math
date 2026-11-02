(** Federer (1969), 3.2.2, p. 242: on the whole normed
    source the continuity hypothesis is precisely class zero.
    This adapter preserves both given norm topologies. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormClassOneUP NormClassZeroTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_continuous_whole_class_zero]: the
    continuity hypothesis of Federer 3.2.2, p. 242,
    expressed in the intrinsic class-zero epsilon laws of 3.1.1,
    p. 210. The whole source is an open domain. *)
Lemma norm_continuous_whole_class_zero (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY) (f:X->Y):
  continuous (fun x:real_norm_metric_space hNX=>(f x:real_norm_metric_space hNY)) ->
  norm_class_zero NX NY setT f.
Proof.
move=>hf a _; split.
- exists 1; split; first exact ltr01; by move=>h hh.
- move=>e he.
  have hball:nbhs (f a:real_norm_metric_space hNY)
      [set z|mdist (f a:real_norm_metric_space hNY) z<e].
    apply:(proj2 (metricType_numDomainType.nbhs_mdistP (f a:real_norm_metric_space hNY) _)).
    exists e=>//; by move=>z hz.
  have hpre:=hf (a:real_norm_metric_space hNX) _ hball.
  have [d hd hb]:=proj1 (metricType_numDomainType.nbhs_mdistP (a:real_norm_metric_space hNX) _) hpre.
  exists d; split; first exact hd.
  move=>h _ hh.
  have hdist:mdist (a:real_norm_metric_space hNX) (a+h)<d.
    change (is_true (NX (a-(a+h))<d)).
    by rewrite opprD addrA subrr add0r (real_seminorm_negate hNX.1).
  have hnear:=hb (a+h) hdist.
  change (is_true (NY (f a-f (a+h))<e)) in hnear.
  by rewrite (real_seminorm_subtract hNY.1).
Qed.
