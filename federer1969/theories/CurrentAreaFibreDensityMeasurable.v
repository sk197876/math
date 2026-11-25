(** Federer (1969), 4.1.25, p. 383: the
    actual full-fibre vector density is Hausdorff
    measurable. Reuse scalar weighted-area integrals and
    the existing finite-coordinate measurability theorem.
    The field is still the independently specified
    opaque partial function, not a coordinate construction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness ExteriorGrading AlternatingForms AlternatingIsomorphism
  AlternatingPairing LinearBasis FiniteDualDimension FiniteCoordinateMeasurability
  CurrentCoefficientNorms CurrentVectorSpaces
  CompactSummableMultivectors CompactSummableMultivectorAmbient
  EuclideanLebesgueDimensions LipschitzUP HausdorffMeasure
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureIntegralGraphEquivalence SummableRealFunctionUP
  ExtendedRealOrderTopology ExtendedFiniteProjectionBorel RealMetricBackground
  PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition
  PartialFunctionExtensionUP PartialFunctionExtensionSealed
  MeasurableFunctionUP MeasurablePostcomposition MeasurableGraphEquivalence
  MeasurableAlmostModification CurrentAreaNormalisedImageSealed
  CurrentAreaFibreDensitySealed CurrentAreaFibreDensityDomain
  CurrentAreaFibreDensityPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FibreDensityMeasurability.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Variables m n : nat.
Local Notation X := (R_n R m).
Local Notation Y := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation V := (exterior_power (R_n R n) m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Variable xi : @compact_summable_multivector_space R h2 m m Full hFull.
Local Notation raw := (@compact_summable_multivector_ambient_value R h2 m m Full hFull xi).
Variable f : X -> R_n R n.
Hypothesis hLip : @is_metric_lipschitz R
  (inner_metric_space (@euclidean_inner_productP R m)) Y setT f.
Local Notation u := (@CurrentAreaNormalisedImage.value R m n f raw).
Local Notation eta := (@CurrentAreaFibreDensity.value R h2 X n m f u).
Local Notation H := (@hausdorff_measure R Y m).
Local Notation M := (@current_vector_mass R h2 n m).
Local Notation hM := (@current_vector_mass_real_norm R h2 n m).

(** Source for [current_area_fibre_representative_measurable]:
    every total representative of the original partial
    fibre density in Federer 4.1.25, p. 383,
    is measurable in its actual coefficient mass norm.
    The finite coordinates are used only in the
    proof; no new basis defines the density. *)
Theorem current_area_fibre_representative_measurable (w : R_n R n -> V) :
  is_partial_function_total_extension eta w ->
  is_measure_measurable_function H
    (partial_function_total (fun y => (w y : real_norm_metric_space hM))).
Proof.
move=> hW.
have hH := @hausdorff_measure_is_measure R Y m.
have [d [b hB]] := @current_vector_finite_basis R h2 n m.
apply: (@finite_coordinate_field_measurable R Y V M hM d b hB H hH w) => i.
pose a := hom_to_form (dual_basis hB i).
have [c [_ hIntegral]] := @current_area_fibre_density_pairing_integral
  R h2 m n xi f hLip w a hW.
have hScalar := @measurable_function_borel_postcomposition R Y
  (extended_real_line R) [the topologicalType of real_line_metric R]
  H hH (real_total_integrand (fun y => pairing (w y) a))
  (fun z => (fine z : real_line_metric R)) hIntegral.1
  (@extended_finite_projection_borel R).
apply: (measurable_function_graph_equivalent _ hScalar) => y z; split.
- move=> [v [hValue <-]].
  move/real_total_integrand_graph: hValue => <-.
  change (dual_basis hB i (w y) = pairing (w y) a).
  by rewrite /a /pairing hom_to_formK.
- move=> hValue.
  exists (pairing (w y) a)%:E; split; first by apply/real_total_integrand_graph.
  change (pairing (w y) a = z).
  by rewrite /a /pairing hom_to_formK.
Qed.

(** Source for [current_area_fibre_density_measurable]:
    measurability of the actual original partial
    fibre density in Federer 4.1.25, p. 383.
    Its conull partial domain is retained, with
    no value assigned at an undefined summand. *)
Theorem current_area_fibre_density_measurable :
  is_measure_measurable_function H
    (eta : partial_function Y (real_norm_metric_space hM)).
Proof.
pose w := @PartialFunctionExtension.value Y V eta 0%R.
have hW : is_partial_function_total_extension eta w :=
  @PartialFunctionExtension.laws Y V eta 0%R.
have hTotal := current_area_fibre_representative_measurable hW.
have hMass : exists c : R, is_measure_integral (@euclidean_lebesgue_measure R m)
    (partial_function_total (fun x =>
      ((@current_vector_mass R h2 m m (raw x))%:E : extended_real_line R))) c%:E.
  exists (@compact_summable_multivector_size R h2 m m Full hFull xi).
  apply: (measure_integral_graph_equivalent _
    (@compact_summable_multivector_ambient_integral R h2 m m Full hFull xi)) => x z.
  exact: real_total_integrand_graph.
have hDomain := @current_area_fibre_density_conull_domain R h2 m n f raw hLip hMass.
apply: (measurable_function_almost_equal (@hausdorff_measure_is_measure R Y m) hTotal).
apply: (measure_almost_everywhere_mono (@hausdorff_measure_is_measure R Y m) _ hDomain)
  => y [v hValue].
exists v; split; first exact: hW y v hValue.
exact: hValue.
Qed.
End FibreDensityMeasurability.
