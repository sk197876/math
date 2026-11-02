(** Federer (1969), 2.10.29, p. 195: existence of the abstract finite
    Euclidean measure-power family. This private recursive witness uses only
    existing opaque product measures and Euclidean block maps. Downstream
    results use the sealed first-factor, measure and successor laws, never
    this recursion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates MeasureUP MetricCartesianRectangleBounds EuclideanMeasurePowerUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section Construction.
Variable R : realType.
Variable d : nat.
Local Notation E n := (inner_metric_space (@euclidean_inner_productP R n)).
Variable nu : set (E d) -> \bar R.
Variable hn : is_measure nu.

(** Source for [euclidean_measure_power_state]: private
    proved-measure recursion witnessing the finite
    products used in 2.10.29, p. 195.
    Every stage carries its measure proof;
    this implementation is hidden by sealing. *)
Fixpoint euclidean_measure_power_state q :
    {mu : set (E (euclidean_power_dimension d q)) -> \bar R | is_measure mu} :=
  match q as k return {mu : set (E (euclidean_power_dimension d k)) -> \bar R | is_measure mu} with
  | 0 => exist _ nu hn
  | k.+1 =>
      let prev := euclidean_measure_power_state k in
      exist _ (paired_product_measure (fun x y=>@euclidean_block_join R (euclidean_power_dimension d k) d (x,y))
        (proj2_sig prev) hn)
        (paired_product_is_measure (fun x y=>@euclidean_block_join R (euclidean_power_dimension d k) d (x,y))
          (proj2_sig prev) hn)
  end.

(** Source for [euclidean_measure_power_family_exists]: supporting
    proved existence of all positive finite
    Euclidean powers of a measure for
    2.10.29, p. 195. No regularity,
    density or mass conclusion is assumed. *)
Theorem euclidean_measure_power_family_exists : exists lambda,
  is_euclidean_measure_power_family hn lambda.
Proof.
exists (fun q=>proj1_sig (euclidean_measure_power_state q)).
refine {| euclidean_measure_power_first := erefl;
  euclidean_measure_power_measure := fun q=>proj2_sig (euclidean_measure_power_state q);
  euclidean_measure_power_successor := _ |}.
move=> q; by [].
Qed.
End Construction.
