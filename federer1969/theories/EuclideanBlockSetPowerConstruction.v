(** Private set-power witness for Federer (1969), 2.10.29, p. 195. The
    recursion witnesses only the stated Cartesian membership laws;
    downstream proofs use the sealed specification. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanMeasurePowerUP EuclideanBlockSetPowerUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section Witness.
Variable R : realType.
Variable d : nat.
Local Notation E n := (inner_metric_space (@euclidean_inner_productP R n)).
Variable C : set (E d).

(** Source for [euclidean_block_set_power_witness]: private
    recursive witness of the Cartesian membership
    laws in 2.10.29, p. 195. It
    is not used by downstream proofs. *)
Fixpoint euclidean_block_set_power_witness q : set (E (euclidean_power_dimension d q)) :=
  match q as k return set (E (euclidean_power_dimension d k)) with
  | 0 => C
  | k.+1 => [set x | @euclidean_block_set_power_witness k (@euclidean_block_split R (euclidean_power_dimension d k) d x).1 /\
      C (@euclidean_block_split R (euclidean_power_dimension d k) d x).2]
  end.

(** Source for [euclidean_block_set_power_exists]: supporting
    proved existence of the finite Cartesian
    set powers in 2.10.29, p. 195. *)
Theorem euclidean_block_set_power_exists : exists U, is_euclidean_block_set_power C U.
Proof. exists (fun q=>@euclidean_block_set_power_witness q); by constructor. Qed.
End Witness.
