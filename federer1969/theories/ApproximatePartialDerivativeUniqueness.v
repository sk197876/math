(** Federer (1969), 3.1.2, p. 212: the approximate partial derivative
    has a unique value, by Hausdorff uniqueness of approximate limits. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import GrassmannAbbreviations RealNormUP NormMetric
  ApproximateLimitUniqueness EuclideanApproximateContext ApproximatePartialDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [approximate_partial_derivative_unique]: supporting
    uniqueness of the value denoted ap D_i f(a) in Federer 3.1.2,
    p. 212, from 2.9.12, p. 158. No completeness of Y is needed. *)
Theorem approximate_partial_derivative_unique (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (A : R_n R n -> Prop)
    (f : R_n R n -> Y) (a : R_n R n) (i : 'I_n) (u v : Y) :
  has_approximate_partial_derivative hNY A f a i u ->
  has_approximate_partial_derivative hNY A f a i v -> u=v.
Proof.
move=> [_ hu] [_ hv].
exact: (measure_approximate_limit_unique (scalar_approximate_context R)
  (@metric_hausdorff R [the metricType R of real_norm_metric_space hNY]) hu hv).
Qed.
