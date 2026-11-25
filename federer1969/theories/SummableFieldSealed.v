(** Federer (1969), 4.1.19, p. 377: opaque carrier
    for the full finite raw L1 field space. The
    independently defined finite-value locus is represented
    by the existing proved linear subspace interface. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric ModuleQuotient
  SubspaceCarrier MeasureUP TotalMeasurableFunctionSpace SummableFieldUP
  LinearSubspaceRepresentationUP LinearSubspaceRepresentationSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type SummableFieldSignature.
(** Source for [space]: the full finite L1 space
    supporting the extension from compact fields in
    Federer 4.1.19, p. 377, with the total-domain
    convention of 2.4.12, pp. 86–87. *)
Parameter space : forall (R : realType) (X : topologicalType)
  (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
  (mu : set X -> \bar R), is_measure mu -> lmodType R.
(** Source for [inclusion]: retain the actual measurable
    representatives of the finite L1 space used in
    Federer 4.1.19, p. 377. *)
Parameter inclusion : forall (R : realType) (X : topologicalType)
  (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
  (mu : set X -> \bar R) (hm : is_measure mu),
  Hom (@space R X V N hN mu hm)
    (subspace_space (@total_measurable_normed_subspace R X V N hN mu hm)).
(** Source for [laws]: the carrier represents exactly
    the independent finite L1 locus, supporting Federer
    4.1.19, p. 377. Its inclusion is injective on
    actual representatives, not on almost-equality classes. *)
Parameter laws : forall (R : realType) (X : topologicalType)
  (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
  (mu : set X -> \bar R) (hm : is_measure mu),
  is_linear_subspace_representation
    (@summable_field_subspace R X V N hN mu hm)
    (@inclusion R X V N hN mu hm).
End SummableFieldSignature.

Module SummableField : SummableFieldSignature.
(** Source for [space]: reuse the proved abstract
    subspace carrier for the L1 extension in
    Federer 4.1.19, p. 377. *)
Definition space (R : realType) (X : topologicalType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) : lmodType R :=
  @LinearSubspaceRepresentation.space R _
    (@summable_field_subspace R X V N hN mu hm).
(** Source for [inclusion]: the existing proved carrier
    preserves the original raw field values, supporting
    Federer 4.1.19, p. 377. *)
Definition inclusion (R : realType) (X : topologicalType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) :
    Hom (@space R X V N hN mu hm)
      (subspace_space (@total_measurable_normed_subspace R X V N hN mu hm)) :=
  @LinearSubspaceRepresentation.inclusion R _
    (@summable_field_subspace R X V N hN mu hm).
(** Source for [laws]: the earlier existence theorem
    supplies the exact subspace laws, supporting the
    full L1 extension in Federer 4.1.19, p. 377. *)
Lemma laws (R : realType) (X : topologicalType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  is_linear_subspace_representation
    (@summable_field_subspace R X V N hN mu hm)
    (@inclusion R X V N hN mu hm).
Proof. exact: (@LinearSubspaceRepresentation.laws R _ _). Qed.
End SummableField.
