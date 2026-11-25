(** Federer (1969), 4.1.4, p. 348: opaque inward loci,
    exposing only the original positive-ball-margin laws.
    Their existence was proved independently before sealing. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import InnerParallelFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type InnerParallelFamilySignature.
(** Source for [value]: the original inward positive-radius
    locus used for C_e, Federer 4.1.4, p. 348. *)
Parameter value:forall (R:realType) (X:lmodType R)
  (NX:X->R) (A:set X),R->set X.
(** Source for [laws]: exact positive-ball-margin laws for the
    original inward loci, Federer 4.1.4, p. 348. *)
Parameter laws:forall (R:realType) (X:lmodType R) (NX:X->R) (A:set X),
  is_inner_parallel_family NX A (@value R X NX A).
End InnerParallelFamilySignature.
Module InnerParallelFamily:InnerParallelFamilySignature.
(** Source for [value]: the proved inward-locus witness is
    hidden for Federer 4.1.4, p. 348. *)
Definition value (R:realType) (X:lmodType R) (NX:X->R) (A:set X):R->set X:=
  projT1 (cid (@inner_parallel_family_exists R X NX A)).
(** Source for [laws]: the opaque witness retains the exact
    independently specified original laws, Federer 4.1.4, p. 348. *)
Lemma laws (R:realType) (X:lmodType R) (NX:X->R) (A:set X):
  is_inner_parallel_family NX A (@value R X NX A).
Proof. exact:(projT2 (cid (@inner_parallel_family_exists R X NX A))). Qed.
End InnerParallelFamily.
