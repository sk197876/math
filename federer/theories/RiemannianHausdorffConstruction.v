(** Existence only for the original-distance Hausdorff
    measure in Federer (1969), 3.2.46, p. 281. Exact
    cutoff and cost compatibility with the finite carrier
    has been proved before this witness is selected. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric RiemannianTensorUP RiemannianMetricCarrier
  RiemannianHausdorffUP RiemannianHausdorffCompatibility RealHausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [riemannian_hausdorff_measure_exists]: existence
    of the measure defined by original-rho coverings in
    3.2.46, p. 281, in every nonnegative real degree. *)
Lemma riemannian_hausdorff_measure_exists (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) (p : R) (hp : 0<=p) :
  exists mu, is_riemannian_hausdorff_measure hg p hp mu.
Proof.
exists (@real_hausdorff_measure R [the metricType R of riemannian_metric_space hg] p hp).
exact: riemannian_hausdorff_carrier_laws.
Qed.
