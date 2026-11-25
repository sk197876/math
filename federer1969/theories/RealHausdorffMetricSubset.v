(** Federer 2.10.26, p. 190: use the existing real-power metric-subspace
    equality with the actual Gamma normalization when restricting a
    fibre argument to a compact image. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import MetricSubsetBackground RealPowerMetricSubset
  RealHausdorffMeasure RealHausdorffNormalisation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_hausdorff_metric_subset_measure]: supporting
    original metric-subspace connection for Federer 2.10.26, p. 190.
    The same actual real degree and Gamma coefficient occur in the
    ambient and induced metrics. Reuse the proved real-power equality
    on arbitrary sets, including infinite masses and degree zero. *)
Theorem real_hausdorff_metric_subset_measure (R : realType) (Y : metricType R)
    (K : set Y) (p : R) (hp : (0<=p)%R) (B : set (metric_subset K)) :
    @real_hausdorff_measure R Y p hp ((fun x : metric_subset K => (val x : Y)) @` B)=
      @real_hausdorff_measure R [the metricType R of metric_subset K] p hp B.
Proof.
exact: (@metric_real_power_metric_subset_measure R Y K
  (real_hausdorff_normalisation hp) p B
  (ltW (real_hausdorff_normalisation_positive hp)) hp).
Qed.
