(** Federer (1969), 2.2.15, p. 70, cites the proof of 2.3.2(6), pp. 73–74,
    to show Borel functions form a Baire class. We use its exact
    open-inner-set formula: points whose distance to the complement exceeds
    1/i. Natural index k represents positive i=k+1. The already sealed
    distance interface of 2.2.10 supplies the distance laws; num_normedtype
    is used only for open real order rays, general topology background. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology num_normedtype.
From Federer Require Import PointwiseLimit RealMetricBackground ExtendedRealReciprocalBounds
  MetricSetDistanceUP MetricSetDistanceBasic MetricSetDistanceClosure MetricSetDistanceContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_open_inner]: the open sets E_i
    in the proof of Federer 2.3.2(6), pp. 73–74,
    explicitly used by 2.2.15, p. 70. The function
    d is the distance to the complement; its abstract laws
    are supplied separately. *)
Definition metric_open_inner (R : realType) (Y : Type) (d : Y -> R) k : set Y :=
  [set y | ((k.+1)%:R)^-1 < d y].

(** Source for [metric_open_inner_open]: supporting openness
    of E_i in Federer 2.3.2(6), p. 73, for
    the Baire-class assertion in 2.2.15, p. 70.
    Distance is continuous and a strict real ray is open. *)
Lemma metric_open_inner_open (R : realType) (Y : metricType R) (A : set Y)
    (d : Y -> R) (hd : is_metric_set_distance A d) k :
  open (metric_open_inner d k).
Proof.
apply: (@open_comp Y [the topologicalType of real_line_metric R]
  d [set t | ((k.+1)%:R)^-1 < t]); last exact: open_gt.
move=> y _; exact: (@metric_set_distance_continuous R Y A d hd y).
Qed.

(** Source for [pointwise_open_preimage_formula]: direct union-
    union-intersection formula in Federer 2.3.2(6), p. 74,
    used by 2.2.15, p. 70. For pointwise convergence
    everywhere, the equality is exact; the measure-theory passage
    uses equality almost everywhere. The whole-space open set is
    handled separately by the caller, avoiding distance to the empty set. *)
Theorem pointwise_open_preimage_formula (R : realType) (X : Type) (Y : metricType R)
    (f : nat -> X -> Y) (g : X -> Y) (U : set Y) (d : Y -> R)
    (hd : is_metric_set_distance (~` U) d) :
  open U -> is_pointwise_limit f g ->
  g @^-1` U = \bigcup_i \bigcup_N \bigcap_(n in [set n | (N <= n)%N])
    (f n @^-1` metric_open_inner d i).
Proof.
move=> ho hlim; apply/seteqP; split.
- move=> x hx.
  have hdpos : 0 < d (g x).
    apply: (@metric_set_distance_positive_outside_closed R Y (~` U) d hd (g x)).
    + exact: open_closedC ho.
    + by move=> hn; exact: hn hx.
  have [i hi] := positive_reciprocal_nat_small hdpos.
  have hnb : nbhs (g x) (metric_open_inner d i).
    have hop := @metric_open_inner_open R Y (~` U) d hd i.
    rewrite openE in hop; exact: hop _ hi.
  have [N _ hN] := hlim x _ hnb.
  exists i; first exact Logic.I.
  exists N; first exact Logic.I.
  move=> n hn; exact: hN n hn.
- move=> x [i _ [N _ hN]]; apply: contrapT=> hx.
  have hd0 : d (g x) = 0 := metric_set_distance_member hd hx.
  have hr : 0 < (((i.+1)%:R : R)^-1) by rewrite invr_gt0 ltr0n.
  have hnb : nbhs (g x) [set y | d y < ((i.+1)%:R)^-1].
    have hnR : nbhs (d (g x) : real_line_metric R)
        [set t : real_line_metric R | t < ((i.+1)%:R)^-1].
      have hop : open [set t : real_line_metric R | t < ((i.+1)%:R)^-1] by exact: open_lt.
      rewrite openE in hop; apply: hop; by rewrite hd0.
    exact: (@metric_set_distance_continuous R Y (~` U) d hd (g x) _ hnR).
  have [M _ hM] := hlim x _ hnb.
  have hlow := hN (maxn N M) (leq_maxl N M).
  have hhigh := hM (maxn N M) (leq_maxr N M).
  have hh := lt_trans hlow hhigh; by rewrite ltxx in hh.
Qed.
