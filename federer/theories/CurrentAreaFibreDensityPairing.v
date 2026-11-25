(** Federer (1969), 4.1.25, p. 383: the
    actual target fibre density has the scalar
    integrals given by the original weighted area
    formula. Every total representative of its conull
    partial graph gives the same integral. The
    original partial density remains unchanged. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness ExteriorGrading AlternatingForms AlternatingPairing
  CurrentCoefficientNorms CompactSummableMultivectors CompactSummableMultivectorAmbient
  EuclideanLebesgueDimensions LipschitzUP HausdorffMeasure
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureIntegralAlmostEquality MeasureIntegralGraphEquivalence
  SummableRealFunctionUP ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic PartialFunctionExtensionUP
  CurrentLipschitzLebesgueActionIntegrand CurrentAreaNormalisedImageSealed
  CurrentAreaFibreSumUP CurrentAreaFibreDensitySealed CurrentAreaFibreDensityDomain
  CurrentAreaPairingQuotientArea.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FibrePairing.
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

(** Source for [current_area_fibre_density_pairing_integral]:
    scalar evaluation of the literal vector fibre
    density in Federer 4.1.25, p. 383.
    Both integrals have the same finite value.
    The total target representative is arbitrary on
    the null complement of the original partial graph. *)
Theorem current_area_fibre_density_pairing_integral (w : R_n R n -> V)
    (a : A_m (R_n R n) R^o m) :
  is_partial_function_total_extension eta w ->
  exists b : R,
    is_measure_integral (@euclidean_lebesgue_measure R m)
      (@current_lipschitz_lebesgue_action_integrand R m n m f raw (fun _ => a)) b%:E /\
    is_measure_integral H (real_total_integrand (fun y => pairing (w y) a)) b%:E.
Proof.
move=> hW.
have [b [hLeft hRight]] := @current_area_pairing_quotient_area_integrals
  R h2 m n f hLip xi a.
have hMass : exists c : R, is_measure_integral (@euclidean_lebesgue_measure R m)
    (partial_function_total (fun x =>
      ((@current_vector_mass R h2 m m (raw x))%:E : extended_real_line R))) c%:E.
  exists (@compact_summable_multivector_size R h2 m m Full hFull xi).
  apply: (measure_integral_graph_equivalent _
    (@compact_summable_multivector_ambient_integral R h2 m m Full hFull xi)) => x z.
  exact: real_total_integrand_graph.
have hDomain := @current_area_fibre_density_conull_domain R h2 m n f raw hLip hMass.
exists b; split; first exact: hLeft.
apply: (measure_integral_almost_equal (@hausdorff_measure_is_measure R Y m) hRight).
apply: (measure_almost_everywhere_mono (@hausdorff_measure_is_measure R Y m) _ hDomain)
  => y [v hValue].
exists (pairing v a)%:E; split.
- exact: ((@CurrentAreaFibreDensity.laws R h2 X n m f u y v).1 hValue) a.
- apply/real_total_integrand_graph.
  by rewrite (hW y v hValue).
Qed.
End FibrePairing.
