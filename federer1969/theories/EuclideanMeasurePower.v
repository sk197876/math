(** Federer (1969), 2.10.29, p. 195: public finite Euclidean measure-power
    family, using only the opaque family specification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  MeasureUP EuclideanMeasurePowerUP EuclideanMeasurePowerSealed MetricCartesianRectangleBounds EuclideanBlockCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [euclidean_measure_power]: public
    Euclidean power measure supporting 2.10.29,
    p. 195. Stage q has q+1 factors;
    the implementation is opaque. *)
Definition euclidean_measure_power (R : realType) d
    (nu : set (inner_metric_space (@euclidean_inner_productP R d)) -> \bar R) (hn : is_measure nu) :=
  @EuclideanMeasurePower.value R d nu hn.

(** Source for [euclidean_measure_power_specification]: direct
    first-factor, measure and successor laws
    for the finite powers in 2.10.29,
    p. 195, from the sealed interface. *)
Lemma euclidean_measure_power_specification (R : realType) d
    (nu : set (inner_metric_space (@euclidean_inner_productP R d)) -> \bar R) (hn : is_measure nu) :
  is_euclidean_measure_power_family hn (@euclidean_measure_power R d nu hn).
Proof. exact: EuclideanMeasurePower.laws. Qed.

(** Source for [euclidean_measure_power_is_measure]: supporting
    measure law at every positive finite
    Cartesian power in 2.10.29, p. 195. *)
Lemma euclidean_measure_power_is_measure (R : realType) d
    (nu : set (inner_metric_space (@euclidean_inner_productP R d)) -> \bar R) (hn : is_measure nu) q :
  is_measure (@euclidean_measure_power R d nu hn q).
Proof. exact (euclidean_measure_power_measure (euclidean_measure_power_specification hn) q). Qed.

(** Source for [euclidean_measure_power_firstE]: supporting
    single-factor evaluation in 2.10.29, p. 195. *)
Lemma euclidean_measure_power_firstE (R : realType) d
    (nu : set (inner_metric_space (@euclidean_inner_productP R d)) -> \bar R) (hn : is_measure nu) :
  @euclidean_measure_power R d nu hn 0%N=nu.
Proof. exact (euclidean_measure_power_first (euclidean_measure_power_specification hn)). Qed.

(** Source for [euclidean_measure_power_successorE]: supporting
    actual Euclidean block-product evaluation for
    2.10.29, p. 195, using only the
    abstract successor law. *)
Lemma euclidean_measure_power_successorE (R : realType) d
    (nu : set (inner_metric_space (@euclidean_inner_productP R d)) -> \bar R) (hn : is_measure nu) q :
  @euclidean_measure_power R d nu hn q.+1=
    paired_product_measure (fun x y=>@euclidean_block_join R (euclidean_power_dimension d q) d (x,y))
      (@euclidean_measure_power_is_measure R d nu hn q) hn.
Proof.
have hh := euclidean_measure_power_successor (euclidean_measure_power_specification hn) q.
have hp : euclidean_measure_power_measure (euclidean_measure_power_specification hn) q=
    @euclidean_measure_power_is_measure R d nu hn q := Prop_irrelevance _ _.
by rewrite hp in hh.
Qed.
