(** Federer (1969), 3.2.33, p. 270: the
    analytic rank bound on a connected analytic manifold.
    The corrected reference to 3.1.24 is applied through
    actual local equations, not postulated as a rank law. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  NormAnalyticRelativeUP AnalyticSubmanifoldUP RelativeLowImageLocus AnalyticRankZeroLocus
  AnalyticChartZeroGlobalAlternative HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [analytic_relative_rank_bound_alternative]: the
    intrinsic rank-set inference in Federer 3.2.33,
    p. 270, with the erratum p. 5 correction
    at book p. 270 line 25. The actual
    relative low-rank locus is either all of W or
    Hausdorff null. Analytic chart equations and connectedness
    prove this alternative for every natural dimension.
    No selected field or additional rank premise is used. *)
Theorem analytic_relative_rank_bound_alternative (R:realType) n m v mu
    (W:set (R_n R n)) (F:R_n R n->R_n R v):
  @is_euclidean_analytic_submanifold R n m W ->
  @norm_analytic_relative R (R_n R n) (R_n R v)
    (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R v))
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R v)) setT W F ->
  @connected (inner_metric_space (@euclidean_inner_productP R n)) W ->
  relative_low_image_locus mu W F = W \/
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m
      (relative_low_image_locus mu W F)=0%E.
Proof.
move=>hW hF hConnected.
exact:(analytic_chart_zero_locus_global_alternative
  (@relative_low_image_analytic_zero_locus R n m v mu W F hW hF) hConnected).
Qed.
