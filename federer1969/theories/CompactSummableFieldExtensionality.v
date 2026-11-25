(** Federer (1969), 4.1.18, pp. 375–376: the
    original compact L1 fields are genuine functions on U.
    Equality of their actual values gives equality of fields;
    this does not assert definiteness of the L1 seminorm. *)
From mathcomp Require Import all_boot all_order all_algebra
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric Hom SubspaceCarrier
  MeasureUP CompactSummableFieldSealed CompactSummableFieldLaws
  LinearSubspaceRepresentationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [compact_summable_field_value_injective]: the
    original field carrier retains all its actual values,
    supporting the degree endpoints in Federer 4.1.18,
    p. 376. Almost equality is not substituted for equality. *)
Theorem compact_summable_field_value_injective (R:realType)
    (X:topologicalType) (V:lmodType R) (N:V->R) (hN:is_real_norm N)
    (mu:set X->\bar R) (hm:is_measure mu):
  injective (@compact_summable_field_value R X V N hN mu hm).
Proof.
move=>f g hValues.
apply:(subspace_representation_injective (@CompactSummableField.laws R X V N hN mu hm)).
apply:subspace_val_injective.
exact:hValues.
Qed.
