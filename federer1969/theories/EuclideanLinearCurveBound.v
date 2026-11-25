(** Federer (1969), 3.2.46, p. 281: the local linear map
    L composed with an admissible curve is Lipschitz. This
    supporting bound uses the actual operator norm of 1.7.6,
    pp. 33--34, including singular maps and zero bounds. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric RealMetricBackground
  OperatorNorm LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_linear_curve_lipschitz_bound]: the
    Lipschitz regularity of L composed with C, used to compare
    with ordinary curve length in Federer 3.2.46, p. 281.
    The domain may be the original interval or the whole line. *)
Lemma euclidean_linear_curve_lipschitz_bound (R : realType) n
    (L : {linear R_n R n -> R_n R n})
    (C : real_line_metric R -> inner_metric_space (@euclidean_inner_productP R n))
    (K : set (real_line_metric R)) ell :
  @is_metric_lipschitz_bound R [the metricType R of real_line_metric R]
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] K C ell ->
  @is_metric_lipschitz_bound R [the metricType R of real_line_metric R]
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] K (fun t=>L (C t))
    (linear_operator_norm (@euclidean_inner_productP R n) (@euclidean_inner_productP R n)
      (@coordinate_basisP R n) L * ell).
Proof.
move=> hC; pose hE := @euclidean_inner_productP R n.
pose M := linear_operator_norm hE hE (@coordinate_basisP R n) L.
have hM : 0 <= M := linear_operator_norm_nonnegative hE hE (@coordinate_basisP R n) L.
split; first exact: mulr_ge0 hM hC.1.
move=> t u ht hu.
have h := linear_operator_norm_bound hE hE (@coordinate_basisP R n) L (C t-C u).
rewrite linearB in h.
have hCu := hC.2 t u ht hu.
rewrite inner_metric_distanceE in hCu *.
apply: le_trans h _; rewrite -mulrA.
exact (ler_wpM2l hM hCu).
Qed.
