(** Federer (1969), 4.1.18, p. 375: opaque compactly
    supported summable fields. The independently specified
    subspace is represented by its existing proved abstract
    linear carrier. Its implementation is not a public field. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric Hom ModuleQuotient
  SubspaceCarrier MeasureUP TotalMeasurableFunctionSpace
  CompactSummableFieldUP LinearSubspaceRepresentationUP
  LinearSubspaceRepresentationSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type CompactSummableFieldSignature.
(** Source for [space]: the space Omega_m of Federer 4.1.18,
    p. 375, with a general normed target allowed as a supporting
    abstraction. No separated norm is imposed on raw fields. *)
Parameter space:forall (R:realType) (X:topologicalType)
  (V:lmodType R) (N:V->R) (hN:is_real_norm N)
  (mu:set X->\bar R),is_measure mu->lmodType R.
(** Source for [inclusion]: actual total measurable values of
    the compactly supported fields in Federer 4.1.18, p. 375. *)
Parameter inclusion:forall (R:realType) (X:topologicalType)
  (V:lmodType R) (N:V->R) (hN:is_real_norm N)
  (mu:set X->\bar R) (hm:is_measure mu),
  Hom (@space R X V N hN mu hm)
    (subspace_space (@total_measurable_normed_subspace R X V N hN mu hm)).
(** Source for [laws]: exact membership, injectivity and full
    representation of Omega_m, supporting the actual q map
    of Federer 4.1.18, p. 375. *)
Parameter laws:forall (R:realType) (X:topologicalType)
  (V:lmodType R) (N:V->R) (hN:is_real_norm N)
  (mu:set X->\bar R) (hm:is_measure mu),
  is_linear_subspace_representation
    (@compact_summable_field_subspace R X V N hN mu hm)
    (@inclusion R X V N hN mu hm).
End CompactSummableFieldSignature.

Module CompactSummableField:CompactSummableFieldSignature.
(** Source for [space]: reuse of the proved abstract subspace
    representation, supporting Omega_m in Federer 4.1.18, p. 375. *)
Definition space (R:realType) (X:topologicalType)
    (V:lmodType R) (N:V->R) (hN:is_real_norm N)
    (mu:set X->\bar R) (hm:is_measure mu):lmodType R:=
  @LinearSubspaceRepresentation.space R _
    (@compact_summable_field_subspace R X V N hN mu hm).
(** Source for [inclusion]: the existing proved linear
    inclusion supporting Omega_m in Federer 4.1.18, p. 375. *)
Definition inclusion (R:realType) (X:topologicalType)
    (V:lmodType R) (N:V->R) (hN:is_real_norm N)
    (mu:set X->\bar R) (hm:is_measure mu):
    Hom (@space R X V N hN mu hm)
      (subspace_space (@total_measurable_normed_subspace R X V N hN mu hm)):=
  @LinearSubspaceRepresentation.inclusion R _
    (@compact_summable_field_subspace R X V N hN mu hm).
(** Source for [laws]: the original membership predicate is
    retained exactly, supporting Federer 4.1.18, p. 375. *)
Lemma laws (R:realType) (X:topologicalType)
    (V:lmodType R) (N:V->R) (hN:is_real_norm N)
    (mu:set X->\bar R) (hm:is_measure mu):
  is_linear_subspace_representation
    (@compact_summable_field_subspace R X V N hN mu hm)
    (@inclusion R X V N hN mu hm).
Proof. exact:(@LinearSubspaceRepresentation.laws R _ _). Qed.
End CompactSummableField.
