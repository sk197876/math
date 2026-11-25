(** Federer (1969), 3.3.13, pp. 297–298: actual projection
    contraction for the printed 2.10.11 appeal. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_projection_lipschitz_one]: supporting actual
    Lip(p)<=1 in Federer 3.3.13, p. 297, proof using 2.10.11, p. 176.
    This is the already proved original projection contraction of
    1.7.7, p. 34, through the actual Euclidean metric; no selected
    projection or operator-bound premise is supplied. *)
Lemma structure_projection_lipschitz_one (R:realType) n m
    (p:euclidean_projection_space R n m):
  @is_metric_lipschitz_bound R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]
    [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]
    setT (euclidean_projection_linear p) 1.
Proof.
split; first exact:ler01.
move=>x y _ _; rewrite mul1r; exact:euclidean_projection_nonexpanding.
Qed.
