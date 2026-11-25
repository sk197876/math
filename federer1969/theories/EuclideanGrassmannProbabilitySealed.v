(** Opaque Grassmann probability used in Federer (1969),
    3.3.1, p. 287. The invariant probability is specified before
    existence, and no selected Haar measure or plane is exported. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanOrthogonalInvariantMeasures
  EuclideanGrassmannProbabilityUP EuclideanGrassmannProbabilityConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type EuclideanGrassmannProbabilitySignature.
(** Source for [value]: gamma_(n,k) used in Federer 3.3.1,
    p. 287, with existence from 2.7.16(6), p. 139. *)
Parameter value:forall (R:realType) n k,(k<=n)%N ->
  set (euclidean_grassmann_space R n k)->\bar R.
(** Source for [laws]: independent invariant-probability laws of
    gamma_(n,k), Federer 3.3.1, p. 287, and 2.7.16(6), p. 139. *)
Parameter laws:forall (R:realType) n k (hkn:(k<=n)%N),
  is_euclidean_grassmann_probability (@value R n k hkn).
End EuclideanGrassmannProbabilitySignature.

Module EuclideanGrassmannProbability:EuclideanGrassmannProbabilitySignature.
(** Source for [value]: private realization of proved invariant
    probability existence for Federer 3.3.1, p. 287. *)
Definition value (R:realType) n k (hkn:(k<=n)%N):=
  projT1 (cid (@euclidean_grassmann_probability_exists R n k hkn)).
(** Source for [laws]: the selected probability satisfies its
    independently stated specification, Federer 3.3.1, p. 287. *)
Lemma laws (R:realType) n k (hkn:(k<=n)%N):
  is_euclidean_grassmann_probability (@value R n k hkn).
Proof. exact:projT2 (cid (@euclidean_grassmann_probability_exists R n k hkn)). Qed.
End EuclideanGrassmannProbability.
