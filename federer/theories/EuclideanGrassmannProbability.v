(** Public gamma_(n,k) of Federer (1969), 2.7.16(6), p. 139,
    used in 3.3.1, p. 287. Its original invariant-probability
    specification is independent of projection-kernel constructions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanOrthogonalInvariantMeasures
  EuclideanGrassmannProbabilityUP EuclideanGrassmannProbabilitySealed MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [euclidean_grassmann_probability]: the actual
    gamma_(n,k) used in Federer 3.3.1, p. 287, as independently
    characterized by 2.7.16(6), p. 139. *)
Definition euclidean_grassmann_probability (R:realType) n k (hkn:(k<=n)%N):=
  @EuclideanGrassmannProbability.value R n k hkn.

(** Source for [euclidean_grassmann_probability_specification]:
    invariant-probability laws for the original gamma_(n,k),
    Federer 3.3.1, p. 287, and 2.7.16(6), p. 139. *)
Lemma euclidean_grassmann_probability_specification (R:realType) n k (hkn:(k<=n)%N):
  is_euclidean_grassmann_probability (@euclidean_grassmann_probability R n k hkn).
Proof. exact:EuclideanGrassmannProbability.laws. Qed.
