(** Opaque witness for the actual theta*_{n,m} of Federer (1969), 2.7.16(6),
    p. 139, used by 2.10.5, p. 172. Only the abstract invariant-probability
    specification is exposed. Source context:
    OrthogonalProjectionProbabilityUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanProjectionMetric OrthogonalProjectionProbabilityUP
  OrthogonalProjectionProbabilityConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type OrthogonalProjectionProbabilitySignature.
(** Source for [value]: abstract witness for theta*
    in Federer 2.10.5, p. 172, from 2.7.16(6),
    p. 139, for m<=n. *)
Parameter value : forall (R : realType) (n m : nat), (m<=n)%N ->
  set (orthogonal_projection_metric_space R n m) -> \bar R.
(** Source for [laws]: the invariant-probability laws
    for the witness used in Federer 2.10.5, p. 172. *)
Parameter laws : forall (R : realType) (n m : nat) (hmn : (m<=n)%N),
  is_orthogonal_projection_probability (@value R n m hmn).
End OrthogonalProjectionProbabilitySignature.

Module OrthogonalProjectionProbability : OrthogonalProjectionProbabilitySignature.
(** Source for [value]: private selection from proved
    existence, supporting Federer 2.10.5, p. 172. *)
Definition value (R : realType) (n m : nat) (hmn : (m<=n)%N) :=
  projT1 (cid (@orthogonal_projection_probability_exists R n m hmn)).
(** Source for [laws]: the selected existence witness
    satisfies the theta* laws required in Federer
    2.10.5, p. 172. *)
Lemma laws (R : realType) (n m : nat) (hmn : (m<=n)%N) :
  is_orthogonal_projection_probability (@value R n m hmn).
Proof. exact: projT2 (cid (@orthogonal_projection_probability_exists R n m hmn)). Qed.
End OrthogonalProjectionProbability.
