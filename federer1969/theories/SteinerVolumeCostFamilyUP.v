(** Federer (1969), 2.10.32, p. 196: the class C of nonempty compact convex
    subsets of Euclidean space whose Lebesgue volume is at least lambda and
    whose exterior-diameter cost is at most mu. Membership is specified by
    exactly these laws; compactness and nonemptiness are already recorded in
    the Hausdorff-space carrier. Subsequent files prove closedness and
    Steiner stability rather than assuming them. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerConvex CompactSetDistanceProfile
  CompactHausdorffMetric EuclideanLebesgueDimensions ExteriorMeasureGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [steiner_volume_cost_family]: direct
    membership specification for C and its two
    displayed bounds in 2.10.32, p. 196.
    Positivity of the thresholds is a separate
    hypothesis of the numerical comparison theorem. *)
Definition steiner_volume_cost_family (R : realType) (n : nat) (lambda mu : R) :
    set (compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n))) :=
  [set K | is_inner_convex (val K) /\
    (lambda%:E<=euclidean_lebesgue_measure n (val K))%E /\
    (exterior_diameter_cost n (val K)<=mu%:E)%E].
