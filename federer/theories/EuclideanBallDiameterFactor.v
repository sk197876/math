(** Concrete Euclidean geometry for the alternative family
    of Federer (1969), 2.10.2(2), p. 171, including
    the zero-dimensional space. The abstract ball-diameter
    laws are established before applying a covering theorem.
    Source comparison: EuclideanBallDiameter.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From mathcomp Require Import lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  MetricDiameterUP MetricDiameter MetricBallDiameterUP EuclideanBallDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_zero_dimensional_diameter]: supporting
    zero-dimensional case of Federer 2.10.2(2), p. 171.
    Every subset of the one-point vector space has diameter
    zero, including the empty subset. *)
Lemma euclidean_zero_dimensional_diameter (R : realType)
    (A : set (inner_metric_space (@euclidean_inner_productP R 0))) :
  extended_metric_diameter A=0%E.
Proof.
have heq (x y : inner_metric_space (@euclidean_inner_productP R 0)) : x=y.
  apply/ffunP=> i; have hi := ltn_ord i; by rewrite ltn0 in hi.
apply/eqP; rewrite eq_le (metric_diameter_nonnegative (extended_metric_diameter_specification A)) andbT.
apply: (metric_diameter_least (extended_metric_diameter_specification A))=> // x y hx hy.
by rewrite (heq x y) mdistxx.
Qed.

(** Source for [euclidean_ball_diameter_factor]: supporting
    realization of all geometric hypotheses for the
    Euclidean open-ball alternative in Federer 2.10.2(2),
    p. 171. Factor zero is essential in dimension zero;
    factor two holds in every positive dimension. *)
Theorem euclidean_ball_diameter_factor (R : realType) (n : nat) :
  @is_metric_ball_diameter_factor R (inner_metric_space (@euclidean_inner_productP R n))
    (if n==0%N then 0 else 2).
Proof.
case: n=> [|n] /=; constructor.
- exact: lexx.
- by move=> a r hr; rewrite mul0r euclidean_zero_dimensional_diameter.
- by move=> a r hr; rewrite mul0r euclidean_zero_dimensional_diameter.
- by rewrite ler0n.
- move=> a r hr; rewrite (@euclidean_closed_ball_diameter R n a r (ltW hr)); congr (_%:E); lra.
- move=> a r hr; rewrite (@euclidean_open_ball_diameter R n a r hr); congr (_%:E); lra.
Qed.
