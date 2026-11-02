(** Federer (1969), 3.2.36, p. 273:
    distance to the whole first-factor cylinder
    bounds distance to the product from below. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import MetricSetDistanceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_set_distance_subset_bound]:
    general metric support for the positive-
    distance coarea source in Federer 3.2.36,
    p. 273, from the infimum laws
    of 2.2.10, p. 66. Enlarging a
    source decreases its actual distance.
    The two independent distance specifications
    prove the inequality without compactness,
    convexity or a selected nearest point. *)
Lemma metric_set_distance_subset_bound (R:realType) (X:metricType R)
    (A B:set X) (d e:X->R):
  A `<=` B ->is_metric_set_distance A d ->is_metric_set_distance B e ->
  forall x,e x<=d x.
Proof.
move=>hSubset hD hE x.
apply:(@metric_set_distance_greatest R X A d hD x (e x))=>a ha.
exact:(@metric_set_distance_lower R X B e hE x a (hSubset a ha)).
Qed.
