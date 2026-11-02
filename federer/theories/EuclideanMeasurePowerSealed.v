(** Opaque existence witness for finite Euclidean measure powers in Federer
    (1969), 2.10.29, p. 195. Expose only the proved family laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  MeasureUP EuclideanMeasurePowerUP EuclideanMeasurePowerConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type EUCLIDEAN_MEASURE_POWER.
(** Source for [value]: abstract finite Euclidean
    measure family supporting 2.10.29, p. 195. *)
Parameter value : forall (R : realType) d
  (nu : set (inner_metric_space (@euclidean_inner_productP R d)) -> \bar R),
  is_measure nu -> forall q,
    set (inner_metric_space (@euclidean_inner_productP R (euclidean_power_dimension d q))) -> \bar R.
(** Source for [laws]: first-factor, measure and
    successor product laws for 2.10.29, p. 195. *)
Parameter laws : forall (R : realType) d
  (nu : set (inner_metric_space (@euclidean_inner_productP R d)) -> \bar R) (hn : is_measure nu),
  is_euclidean_measure_power_family hn (@value R d nu hn).
End EUCLIDEAN_MEASURE_POWER.
Module EuclideanMeasurePower : EUCLIDEAN_MEASURE_POWER.
(** Source for [value]: private existence witness
    for 2.10.29, p. 195, hidden by
    opaque module ascription. *)
Definition value (R : realType) d
    (nu : set (inner_metric_space (@euclidean_inner_productP R d)) -> \bar R) (hn : is_measure nu) :=
  projT1 (cid (@euclidean_measure_power_family_exists R d nu hn)).
(** Source for [laws]: proved family specification
    for 2.10.29, p. 195; the recursion
    is not exposed. *)
Lemma laws (R : realType) d
    (nu : set (inner_metric_space (@euclidean_inner_productP R d)) -> \bar R) (hn : is_measure nu) :
  is_euclidean_measure_power_family hn (@value R d nu hn).
Proof. exact: projT2 (cid (@euclidean_measure_power_family_exists R d nu hn)). Qed.
End EuclideanMeasurePower.
