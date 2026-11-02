(** Federer (1969), 2.10.43, printed p. 201: the prescribed closed Euclidean
    balls are compact. This supporting adapter applies the project's proved
    finite-basis closed-bounded compactness from 1.7.1, p. 28, to the actual
    metric closed-ball predicate. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerNormInequalities InnerMetric InnerFiniteCompactness MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_closed_metric_ball_compact]: supporting
    compactness of each prescribed ball in 2.10.43,
    p. 201. Ambient dimension zero and nonpositive
    radii are allowed; compactness follows from the
    already proved finite-dimensional metric topology. *)
Lemma euclidean_closed_metric_ball_compact (R : realType) n
    (b : inner_metric_space (@euclidean_inner_productP R n)) (r : R) :
  compact (metric_closed_ball b r).
Proof.
apply: (@inner_finite_basis_boundedly_compact R (R_n R n) _ (@euclidean_inner_productP R n)
  n (@coordinate_basis R n) (@coordinate_basisP R n)); first exact: metric_closed_ball_closed.
exists (inner_norm (@euclidean_inner_productP R n) b+r)=> x hx.
have hdist : mdist x b<=r by rewrite metric_sym; exact hx.
change (is_true (inner_norm (@euclidean_inner_productP R n) (x-b)<=r)) in hdist.
have hh := @inner_norm_triangle R (R_n R n) _ (@euclidean_inner_productP R n) (x-b) b.
rewrite subrK in hh; apply: le_trans hh _; rewrite addrC lerD2l; exact hdist.
Qed.
