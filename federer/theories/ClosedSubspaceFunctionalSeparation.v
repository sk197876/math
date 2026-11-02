(** Supporting Hahn–Banach background for the separability reduction in
    Federer (1969), 2.9.22, p. 167: continuous functionals separate points
    from closed vector subspaces. This consequence is proved from the book's
    Hahn–Banach theorem, 2.4.12, p. 86, and the abstract distance laws of
    2.2.10, p. 66. Neither reference states the entire reflexive-space
    argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology.
From Federer Require Import ModuleQuotient RealNormUP NormMetric
  MetricSetDistanceUP MetricSetDistanceSealed MetricSetDistanceBasic MetricSetDistanceClosure
  SubspaceDistanceSeminorm SeminormNormingFunctional ContinuousRealFunctional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [closed_subspace_continuous_separation]: supporting
    separation used to justify Federer's reflexive separability
    reduction, 2.9.22, p. 167. A point outside a closed
    subspace admits a continuous real linear functional vanishing
    on the subspace and strictly positive at that point.
    Applying Hahn–Banach to the distance seminorm proves this
    without a nearest-point or finite-dimensional assumption. *)
Theorem closed_subspace_continuous_separation (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (Z : subspace E) (x : E) :
  closed (fun y : real_norm_metric_space hN => Z y) -> ~ Z x ->
  exists a : {linear E -> R^o}, is_continuous_real_functional hN a /\
    (forall z, Z z -> a z=0) /\ 0<a x.
Proof.
move=> hZ hx.
pose A : set (real_norm_metric_space hN) := fun y => Z y.
have hn : A !=set0 by exists 0; exact: subspace_zero.
pose d := MetricSetDistance.value hn.
have hd := MetricSetDistance.laws hn.
have hs := @subspace_distance_is_seminorm R E N hN Z d hd.
have [a [ha hax]] := seminorm_norming_functional hs x.
have hb z : `|a z|<=N z.
  have hh := metric_set_distance_lower hd z (subspace_zero Z).
  change (is_true (d z<=N (z-0))) in hh.
  rewrite subr0 in hh; exact: le_trans (ha z) hh.
exists a; split.
  apply: (@bounded_real_functional_continuous R E N hN a 1 ler01).
  by move=> z; rewrite mul1r; exact: hb.
split.
  move=> z hz; have hh := ha z.
  change (is_true (`|a z|<=d z)) in hh.
  rewrite /d in hh.
  rewrite (metric_set_distance_member hd hz) in hh.
  have hzero : `|a z|=0 by apply/le_anti; rewrite hh normr_ge0.
  by move/eqP: hzero; rewrite normr_eq0=> /eqP.
rewrite hax.
exact (@metric_set_distance_positive_outside_closed R
  [the metricType R of real_norm_metric_space hN] A d hd x hZ hx).
Qed.
