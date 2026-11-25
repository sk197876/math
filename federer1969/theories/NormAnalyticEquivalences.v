(** Federer (1969), 3.1.24, pp. 237–239:
    equivalence of the four definitions of analyticity. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP NormAnalyticUP
  NormAnalyticDiagonal NormAnalyticTaylor NormAnalyticPolynomialSeries NormPolynomialSeriesAnalytic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [norm_analytic_equivalences]: the four equivalent
    conditions (1)–(4) in Federer 3.1.24, pp. 237–239.
    The cycle of proved implications identifies operator bounds,
    diagonal bounds, uniform Taylor convergence, and uniform
    homogeneous polynomial expansions on actual neighbourhoods.
    Completeness of the target is used for the converse;
    no completeness of the source is needed. *)
Theorem norm_analytic_equivalences (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (hcomplete:is_complete_metric_space (real_norm_metric_space hNY))
    (A:X->Prop) (f:X->Y) a :
  (@norm_analytic_at R X Y NX NY hNX hNY A f a <->
    @norm_diagonal_analytic_at R X Y NX NY hNX hNY A f a) /\
  (@norm_analytic_at R X Y NX NY hNX hNY A f a <->
    @norm_taylor_analytic_at R X Y NX NY hNX hNY A f a) /\
  (@norm_analytic_at R X Y NX NY hNX hNY A f a <->
    @norm_polynomial_analytic_at R X Y NX NY hNX hNY A f a).
Proof.
have h12:=@norm_analytic_diagonal R X Y NX NY hNX hNY A f a.
have h23:=@norm_diagonal_analytic_taylor R X Y NX NY hNX hNY A f a.
have h34:=@norm_taylor_analytic_polynomial R X Y NX NY hNX hNY A f a.
have h41:=@norm_polynomial_series_analytic R X Y NX NY hNX hNY hcomplete A f a.
split.
- split; first exact h12.
  move=>h; exact (h41 (h34 (h23 h))).
- split.
  + split.
    * move=>h; exact (h23 (h12 h)).
    * move=>h; exact (h41 (h34 h)).
  + split.
    * move=>h; exact (h34 (h23 (h12 h))).
    * exact h41.
Qed.
