(** Local proof correction for Federer (1969), 2.10.31, p. 196, first
    paragraph, the line following the reflected-cap formula. The scan prints
    T_k contained in B(a,s) with s<r; the shrinking centred-ball argument
    needs B(0,s). This is not an entry in the working May 1987 erratum. The
    theorem itself is unchanged. The concrete example below refutes the
    printed-centre inference from compact containment and absence of
    boundary points. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerNormedTopology EuclideanOneCoordinate
  EuclideanBallVolume MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [shrinking_ball_wrong_center_counterexample]: local
    counterexample to the intermediate printed centre
    in 2.10.31, p. 196. The origin singleton
    is compact, lies in the centred unit ball
    and avoids its distance sphere. For a point
    a on that sphere it cannot lie in any
    closed ball about a of radius less than one.
    This is not a counterexample to the theorem. *)
Theorem shrinking_ball_wrong_center_counterexample (R : realType) :
  exists a : inner_metric_space (@euclidean_inner_productP R 1),
    mdist (0 : inner_metric_space (@euclidean_inner_productP R 1)) a= 1 /\
    compact ([set 0] : set (inner_metric_space (@euclidean_inner_productP R 1))) /\
    ([set 0] : set (inner_metric_space (@euclidean_inner_productP R 1))) !=set0 /\
    ([set 0] : set (inner_metric_space (@euclidean_inner_productP R 1))) `<=` metric_closed_ball (0 : inner_metric_space (@euclidean_inner_productP R 1)) 1 /\
    ([set 0] : set (inner_metric_space (@euclidean_inner_productP R 1))) `&` [set x : inner_metric_space (@euclidean_inner_productP R 1) | mdist (0 : inner_metric_space (@euclidean_inner_productP R 1)) x= 1]=set0 /\
    forall s : R, s<1 -> ~(([set 0] : set (inner_metric_space (@euclidean_inner_productP R 1))) `<=`
      metric_closed_ball a s).
Proof.
pose E := inner_metric_space (@euclidean_inner_productP R 1).
pose a : E := euclidean_one_embed 1.
have hd : mdist (0 : E) a= 1.
  by rewrite inner_metric_normE subr0 euclidean_norm_one /a /euclidean_one_embed ffunE normr1.
exists a; split=> //; split; first exact: compact_set1.
split; first by exists 0.
split.
- by move=> x ->; rewrite /metric_closed_ball /= mdistxx ler01.
split.
- apply/seteqP; split=> x; last by case.
  move=> [hx hh]; change (x=(0 : E)) in hx.
  change (mdist (0 : E) x= 1) in hh; rewrite hx mdistxx in hh.
  have hne : (0 : R)!= 1 by rewrite eq_sym oner_eq0.
  by move/eqP: hh; rewrite (negbTE hne).
- move=> s hs hsub.
  have hh := hsub 0 erefl.
  change (is_true (mdist a (0 : E)<=s)) in hh.
  rewrite (metric_sym a 0) hd in hh.
  have hbad := lt_le_trans hs hh; by rewrite ltxx in hbad.
Qed.
