(** Federer (1969), 3.2.36, p. 273: exact image
    geometry controls the diameter of a target generator's preimage. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground MetricDiameter MetricIsometricImageGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_isometric_preimage_diameter]: the reverse
    cover cutoff inequality for Q_1 in Federer 3.2.36, p. 273.
    The actual preimage's image is contained in the target set;
    proved image diameter equality and ordinary diameter monotonicity
    give the bound. Empty or unbounded target sets are allowed. *)
Lemma metric_isometric_preimage_diameter (R:realType) (X Y:metricType R) (f:X->Y):
  (forall x y,mdist (f x) (f y)=mdist x y) ->forall B,
    extended_metric_diameter (f @^-1` B)<=extended_metric_diameter B.
Proof.
move=>hMetric B.
rewrite -(@metric_isometric_image_diameter R X Y f hMetric (f @^-1` B)).
apply:extended_metric_diameter_mono=>y [x hx <-]; exact hx.
Qed.
