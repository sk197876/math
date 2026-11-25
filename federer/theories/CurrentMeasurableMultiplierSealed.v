(** Federer (1969), 4.1.7, pp. 355–356:
    opaque measurable current products. The public
    laws expose only the original test action
    and integration representability; the existence
    witness and its construction remain private. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom TensorUP RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading CurrentDomain CurrentSpaces
  CurrentCoefficientNorms CurrentIntegrationCriterion NormalisedCurrentSealed
  NormBoundedBilinearUP VectorDaniellHypotheses CurrentMeasurableMultiplierUP CurrentMeasurableMultiplierExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type CurrentMeasurableMultiplierSignature.
(** Source for [value]: the original measurable
    product current, Federer 4.1.7, pp. 355–356. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) (n q p:nat)
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (V:lmodType R) (NV:V->R) (hNV:is_real_norm NV) (hSepV:is_separable_normed_space hNV)
    (F:exterior_power (R_n R n) q->V->exterior_power (R_n R n) p)
    (hF:norm_bounded_bilinear (@current_vector_mass R h2 n q) NV (@current_vector_mass R h2 n p) F)
    (T:@current_space R h2 n U hU q)
    (hT:@is_integration_representable_current R h2 n q U hU T)
    (f:current_domain R n U->V)
    (hField:is_locally_summable_current_field hNV (@NormalisedCurrent.measure R h2 n q U hU T hT) f),
  @current_space R h2 n U hU p.
(** Source for [laws]: every original test
    has the specified integral action, and
    the resulting current is represented by
    integration, Federer 4.1.7, pp. 355–356. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) (n q p:nat)
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (V:lmodType R) (NV:V->R) (hNV:is_real_norm NV) (hSepV:is_separable_normed_space hNV)
    (F:exterior_power (R_n R n) q->V->exterior_power (R_n R n) p)
    (hF:norm_bounded_bilinear (@current_vector_mass R h2 n q) NV (@current_vector_mass R h2 n p) F)
    (T:@current_space R h2 n U hU q)
    (hT:@is_integration_representable_current R h2 n q U hU T)
    (f:current_domain R n U->V)
    (hField:is_locally_summable_current_field hNV (@NormalisedCurrent.measure R h2 n q U hU T hT) f),
  @is_current_measurable_multiplier R h2 n q p U hU V F T hT f
    (@value R h2 n q p U hU V NV hNV hSepV F hF T hT f hField) /\
  @is_integration_representable_current R h2 n p U hU
    (@value R h2 n q p U hU V NV hNV hSepV F hF T hT f hField).
End CurrentMeasurableMultiplierSignature.
Module CurrentMeasurableMultiplier:CurrentMeasurableMultiplierSignature.
(** Source for [value]: hide the proved
    measurable-product existence witness, supporting
    Federer 4.1.7, pp. 355–356. *)
Definition value (R:realType) (h2:(1+1:R)!=0) (n q p:nat)
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (V:lmodType R) (NV:V->R) (hNV:is_real_norm NV) (hSepV:is_separable_normed_space hNV)
    (F:exterior_power (R_n R n) q->V->exterior_power (R_n R n) p)
    (hF:norm_bounded_bilinear (@current_vector_mass R h2 n q) NV (@current_vector_mass R h2 n p) F)
    (T:@current_space R h2 n U hU q)
    (hT:@is_integration_representable_current R h2 n q U hU T)
    (f:current_domain R n U->V)
    (hField:is_locally_summable_current_field hNV (@NormalisedCurrent.measure R h2 n q U hU T hT) f):
    @current_space R h2 n U hU p:=
  projT1 (cid (@current_measurable_multiplier_exists R h2 n q p U hU V NV hNV hSepV F hF T hT f hField)).
(** Source for [laws]: the hidden witness
    satisfies the independently stated original
    product laws, Federer 4.1.7, pp. 355–356. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) (n q p:nat)
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (V:lmodType R) (NV:V->R) (hNV:is_real_norm NV) (hSepV:is_separable_normed_space hNV)
    (F:exterior_power (R_n R n) q->V->exterior_power (R_n R n) p)
    (hF:norm_bounded_bilinear (@current_vector_mass R h2 n q) NV (@current_vector_mass R h2 n p) F)
    (T:@current_space R h2 n U hU q)
    (hT:@is_integration_representable_current R h2 n q U hU T)
    (f:current_domain R n U->V)
    (hField:is_locally_summable_current_field hNV (@NormalisedCurrent.measure R h2 n q U hU T hT) f):
  @is_current_measurable_multiplier R h2 n q p U hU V F T hT f
    (@value R h2 n q p U hU V NV hNV hSepV F hF T hT f hField) /\
  @is_integration_representable_current R h2 n p U hU
    (@value R h2 n q p U hU V NV hNV hSepV F hF T hT f hField).
Proof.
exact:(projT2 (cid (@current_measurable_multiplier_exists R h2 n q p U hU V NV hNV hSepV F hF T hT f hField))).
Qed.
End CurrentMeasurableMultiplier.
