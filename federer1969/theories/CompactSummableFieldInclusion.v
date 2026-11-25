(** Federer (1969), 4.1.19, p. 377: extend a
    bounded functional from the original Omega space
    to all finite raw L1 fields with the same bound.
    The existing corestriction and seminorm Hahn–Banach
    theorems supply the maps; no Banach quotient is needed. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric ModuleQuotient
  SubspaceCarrier MeasureUP TotalMeasurableFunctionSpace
  LinearSubspaceRepresentationUP LinearSubspaceLiftSealed
  BoundedFunctionalExtension CompactSummableFieldUP CompactSummableFieldSealed
  CompactSummableFieldLaws SummableFieldUP SummableFieldSealed SummableFieldLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section CompactSummableFieldInclusion.
Variable R : realType.
Variable X : topologicalType.
Variable V : lmodType R.
Variable N : V -> R.
Variable hN : is_real_norm N.
Variable mu : set X -> \bar R.
Hypothesis hm : is_measure mu.
Local Notation A :=
  [the lmodType R of
    subspace_space (@total_measurable_normed_subspace R X V N hN mu hm)].
Local Notation W := (@SummableField.space R X V N hN mu hm).
Local Notation C := (@CompactSummableField.space R X V N hN mu hm).
Local Notation inc := (@SummableField.inclusion R X V N hN mu hm).
Local Notation hW := (@SummableField.laws R X V N hN mu hm).
Local Notation incC := (@CompactSummableField.inclusion R X V N hN mu hm).
Local Notation hC := (@CompactSummableField.laws R X V N hN mu hm).
Local Notation S := (@summable_field_subspace R X V N hN mu hm).
Local Notation size := (@summable_field_size R X V N hN mu hm).
Local Notation sizeC := (@compact_summable_field_size R X V N hN mu hm).

(** Source for [compact_summable_field_in_full_lone]:
    the original compact fields of 4.1.18, p. 375,
    lie in the full L1 space used for extension
    in Federer 4.1.19, p. 377. *)
Lemma compact_summable_field_in_full_lone (f : C) : S (incC f).
Proof. exact: (subspace_representation_member hC f).1. Qed.

(** Source for [compact_summable_field_inclusion]:
    the original Omega inclusion into all finite
    L1 fields, supporting Federer 4.1.19, p. 377.
    The existing opaque corestriction preserves every
    raw field value. *)
Definition compact_summable_field_inclusion : Hom C W :=
  @LinearSubspaceLift.map R C W A S inc hW incC
    compact_summable_field_in_full_lone.

(** Source for [compact_summable_field_inclusion_evaluation]:
    inclusion preserves the actual original field,
    supporting the extension in 4.1.19, p. 377. *)
Lemma compact_summable_field_inclusion_evaluation (f : C) :
  inc (compact_summable_field_inclusion f) = incC f.
Proof. exact: (@LinearSubspaceLift.evaluation R C W A S inc hW incC
  compact_summable_field_in_full_lone f). Qed.

(** Source for [compact_summable_field_inclusion_injective]:
    Omega is included as actual fields, supporting
    Federer 4.1.19, p. 377. No identification by
    almost equality is assumed for this inclusion. *)
Lemma compact_summable_field_inclusion_injective :
  injective compact_summable_field_inclusion.
Proof.
move=> f g hEqual; apply: (subspace_representation_injective hC).
have h := congr1 inc hEqual.
by rewrite !compact_summable_field_inclusion_evaluation in h.
Qed.

(** Source for [compact_summable_field_inclusion_size]:
    the inclusion preserves the original L1 size
    exactly, supporting the norm-preserving extension
    in Federer 4.1.19, p. 377. *)
Lemma compact_summable_field_inclusion_size (f : C) :
  size (compact_summable_field_inclusion f) = sizeC f.
Proof.
by rewrite /summable_field_size /compact_summable_field_size
  compact_summable_field_inclusion_evaluation.
Qed.

(** Source for [compact_summable_bounded_functional_extension]:
    the dominated L1 extension used with 2.5.9
    in Federer 4.1.19, p. 377. The original
    nonnegative bound is unchanged. The raw-field L1
    size is a seminorm; no separated-space or
    completeness hypothesis is added. *)
Theorem compact_summable_bounded_functional_extension
    (beta : Hom C R^o) (c : R) :
  0 <= c -> (forall f, `|beta f| <= c*sizeC f) ->
  exists F : Hom W R^o,
    (forall f, F (compact_summable_field_inclusion f) = beta f) /\
    forall g, `|F g| <= c*size g.
Proof.
move=> hNonnegative hBound.
have hOriginal : forall f,
    `|beta f| <= c*size (compact_summable_field_inclusion f).
  by move=> f; rewrite compact_summable_field_inclusion_size; exact: hBound.
have [F [hAgree hF]] := @bounded_functional_extension R C W size
  (@summable_field_size_seminorm R X V N hN mu hm)
  (hom_as_linear compact_summable_field_inclusion)
  compact_summable_field_inclusion_injective
  (hom_as_linear beta) c hNonnegative hOriginal.
exists (hom_of_linear F); split; first exact: hAgree.
exact: hF.
Qed.
End CompactSummableFieldInclusion.
