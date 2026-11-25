(** Federer (1969), 4.1.7, pp. 355–356:
    locally variation-summable fields define actual
    represented current products. Reuse the original
    normalized density, finite bilinear bound and
    arbitrary-open density-current existence theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import AlternatingPairing Hom TensorUP RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms CurrentDomain
  CurrentCoefficientNorms CurrentVectorSpaces CurrentSpaces CurrentEvaluation CurrentIntegrationCriterion
  NormalisedCurrentSealed DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  CurrentDensityNormMeasurable CurrentMeasurableMultiplierUP UnitBilinearLocalIntegral
  MeasurableBoundedBilinearProduct NormBoundedBilinearUP VectorDaniellHypotheses FiniteNormMetricPolish
  OpenCurrentDensityUP OpenCurrentDensitySealed MultivectorDualSealed
  PartialFunctionBasic MeasureUP RadonMeasureUP RadonBorelRegularity MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralUniqueness MeasureSubsetIntegral SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentMeasurableMultiplierExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n q p:nat.
Local Notation X := (R_n R n).
Local Notation Z := (fun m=>exterior_power X m).
Local Notation NZ := (fun m=>@current_vector_mass R h2 n m).
Local Notation hNZ := (fun m=>@current_vector_mass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation UT := (current_domain R n U).
Variable V:lmodType R.
Variable NV:V->R.
Hypothesis hNV:is_real_norm NV.
Hypothesis hSepV:is_separable_normed_space hNV.
Variable F:Z q->V->Z p.
Hypothesis hF:norm_bounded_bilinear (NZ q) NV (NZ p) F.
Variable T:@current_space R h2 n U hU q.
Hypothesis hT:@is_integration_representable_current R h2 n q U hU T.
Local Notation mu := (@NormalisedCurrent.measure R h2 n q U hU T hT).
Local Notation eta := (@NormalisedCurrent.auxiliary_density R h2 n q U hU T hT).
Local Notation hRepresentation := (@NormalisedCurrent.laws R h2 n q U hU T hT).
Local Notation hBase := (normalised_distribution_representation_laws hRepresentation).
Local Notation hm := (distribution_representation_measure hBase).
Local Notation hr := (distribution_representation_radon hBase).
Variable f:UT->V.
Hypothesis hField:is_locally_summable_current_field hNV mu f.

(** Source for [current_measurable_multiplier_density_integrable]:
    the actual product density satisfies every
    original arbitrary-open input condition,
    supporting Federer 4.1.7, pp. 355–356.
    No continuity of the input field is used. *)
Lemma current_measurable_multiplier_density_integrable:
  @is_locally_integrable_open_current_density R h2 n p U mu (fun x=>F (eta x) (f x)).
Proof.
have [d [e he]]:=@current_vector_finite_basis R h2 n q.
have hSep:=@finite_norm_metric_separable R (Z q) (NZ q) (hNZ q) d e he.
have hEta:=@current_density_mass_topology_measurable R h2 n q UT mu hm eta
  (distribution_representation_weak_measurable hBase).
have hProduct:=@measurable_bounded_bilinear_product R UT (Z q) V (Z p)
  (NZ q) NV (NZ p) (hNZ q) hNV (hNZ p) mu hm F hF eta f hSep hSepV hEta hField.1.
split.
- exact:(@current_density_weak_topology_measurable R h2 n p UT mu hm _ hProduct).
- move=>K hK.
  exact:(@unit_bilinear_subset_norm_integral R UT (Z q) V (Z p)
    (NZ q) NV (NZ p) (hNZ q) hNV (hNZ p) mu hm F hF eta f K
    hSep hSepV hEta hField.1 (normalised_distribution_density_unit_bound hRepresentation)
    (radon_compact_measurable hm hr hK) (hField.2 K hK)).
Qed.

(** Source for [current_measurable_multiplier_exists]:
    the specified measurable product is an actual
    integration-representable current, Federer
    4.1.7, pp. 355–356. The original test
    topology is inherited from the proved
    arbitrary-open integration constructor. *)
Theorem current_measurable_multiplier_exists:
  exists S:@current_space R h2 n U hU p,
    @is_current_measurable_multiplier R h2 n q p U hU V F T hT f S /\
    @is_integration_representable_current R h2 n p U hU S.
Proof.
pose S:=@OpenCurrentDensity.value R h2 n p U hU mu hm hr
  (fun x=>F (eta x) (f x)) current_measurable_multiplier_density_integrable.
have hS:=@OpenCurrentDensity.laws R h2 n p U hU mu hm hr
  (fun x=>F (eta x) (f x)) current_measurable_multiplier_density_integrable.
exists S;split.
- move=>psi.
  have hAction:=distribution_representation_action hS psi.
  have hPoint:(fun x=>@MultivectorDual.evaluation R X p (F (eta x) (f x))
      (@current_test_value R h2 n U hU p psi (set_val x)))=
    (fun x=>pairing (F (eta x) (f x)) (@current_test_value R h2 n U hU p psi (set_val x))).
    apply:funext=>x;exact:MultivectorDual.laws.
  by rewrite hPoint in hAction.
- by exists mu,(fun x=>F (eta x) (f x)).
Qed.
End CurrentMeasurableMultiplierExistence.

(** Source for [current_measurable_multiplier_unique]:
    every original test action determines the
    measurable product uniquely, supporting
    Federer 4.1.7, pp. 355–356. *)
Theorem current_measurable_multiplier_unique (R:realType) (h2:(1+1:R)!=0)
    n q p U hU (V:lmodType R)
    (F:exterior_power (R_n R n) q->V->exterior_power (R_n R n) p)
    T hT f (S Q:@current_space R h2 n U hU p):
  @is_current_measurable_multiplier R h2 n q p U hU V F T hT f S ->
  @is_current_measurable_multiplier R h2 n q p U hU V F T hT f Q ->S=Q.
Proof.
move=>hS hQ;apply:(@current_values_extensional R h2 n p U hU)=>psi.
exact:(congr1 (@fine R) (measure_integral_unique (hS psi) (hQ psi))).
Qed.
