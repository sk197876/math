(** Federer (1969), 4.1.18, p. 375: every
    xi in Omega_m gives the actual current Lebesgue^n
    wedge xi. Reuse the arbitrary-open Radon density
    constructor of 4.1.7, pp. 355–358. Its mass is
    the original L1 integral, with no extra boundedness
    or smoothness premise on xi. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading CurrentDomain CurrentSpaces CurrentCoefficientNorms
  CurrentDensityNormMeasurable CurrentIntegrationCriterion OpenCurrentDensityUP
  OpenCurrentDensitySealed CurrentDensityVariation CurrentMassRepresentation
  CurrentMassSealed NormalisedCurrentSealed EuclideanOpenDomainMeasure
  CompactSummableFieldLaws CompactSummableFieldIntegral CompactSummableMultivectors
  MeasureUP RadonMeasureUP RadonBorelRegularity MeasureIntegralUP
  MeasureIntegralBounds MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  MeasureSubsetIntegral MeasureDensity SummableRealFunctionUP SummableSubsetRestriction
  PartialFunctionBasic PartialZeroExtension PartialZeroExtensionLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Density.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation UT:=(current_domain R n U).
Local Notation V:=(exterior_power X m).
Local Notation VN:=(@current_vector_mass R h2 n m).
Local Notation hVN:=(@current_vector_mass_real_norm R h2 n m).
Local Notation mu:=(@euclidean_open_domain_measure R n U).
Local Notation hMu:=(proj1 (@euclidean_open_domain_measure_laws R n U hU)).
Local Notation hRadon:=(proj2 (@euclidean_open_domain_measure_laws R n U hU)).
Local Notation W:=(@compact_summable_multivector_space R h2 n m U hU).
Local Notation value:=(@compact_summable_multivector_value R h2 n m U hU).
Local Notation size:=(@compact_summable_multivector_size R h2 n m U hU).

(** Source for [compact_summable_multivector_density_integrable]:
    Omega_m's original summability supplies every local
    input condition of 4.1.7 for the first summand
    of q in Federer 4.1.18, p. 375. *)
Theorem compact_summable_multivector_density_integrable (xi:W):
  @is_locally_integrable_open_current_density R h2 n m U mu (value xi).
Proof.
have hMeas:=@compact_summable_field_measurable R UT V VN hVN mu hMu xi.
split.
- exact:(@current_density_weak_topology_measurable R h2 n m UT mu hMu
    (value xi) hMeas.1).
- move=>K hK.
  have hSummable:is_measure_summable mu
      (real_total_integrand (fun x=>VN (value xi x))).
    exists (size xi).
    exact:(@compact_summable_field_size_integral R UT V VN hVN mu hMu xi).
  exact:(@summable_measurable_zero_extension R UT mu hMu K
    (real_total_integrand (fun x=>VN (value xi x)))
    (radon_compact_measurable hMu hRadon hK) hSummable).
Qed.

(** Source for [compact_summable_multivector_current]: the
    actual Lebesgue^n wedge xi in the original open U,
    Federer 4.1.18, p. 375. The reused current
    constructor already has a sealed interface. *)
Definition compact_summable_multivector_current (xi:W):
    @current_space R h2 n U hU m:=
  @OpenCurrentDensity.value R h2 n m U hU mu hMu hRadon
    (value xi) (compact_summable_multivector_density_integrable xi).

(** Source for [compact_summable_multivector_current_representation]:
    the original-U integration action for every test,
    supporting q in Federer 4.1.18, p. 375.
    Representation is derived from summability. *)
Theorem compact_summable_multivector_current_representation (xi:W):
  @is_current_integration_representation R h2 n m U hU
    (compact_summable_multivector_current xi) mu (value xi).
Proof. exact:(@OpenCurrentDensity.laws R h2 n m U hU mu hMu hRadon
  (value xi) (compact_summable_multivector_density_integrable xi)). Qed.

(** Source for [compact_summable_multivector_current_representable]:
    the current entering q is representable by integration,
    Federer 4.1.18, p. 375, through 4.1.7. *)
Theorem compact_summable_multivector_current_representable (xi:W):
  @is_integration_representable_current R h2 n m U hU
    (compact_summable_multivector_current xi).
Proof. exists mu,(value xi);exact:compact_summable_multivector_current_representation. Qed.

(** Source for [compact_summable_multivector_current_mass]:
    the mass of Lebesgue^n wedge xi equals integral_U
    mass(xi), the original cost used for the first
    proposition in Federer 4.1.18, p. 375. *)
Theorem compact_summable_multivector_current_mass (xi:W):
  @CurrentMass.value R h2 n m U hU
    (compact_summable_multivector_current xi)=(size xi)%:E.
Proof.
pose T:=compact_summable_multivector_current xi.
pose hT:=compact_summable_multivector_current_representable xi.
rewrite (@current_represented_mass_total R h2 n m U hU T hT).
rewrite (@current_open_density_variation R h2 n m U hU mu hMu hRadon
  (value xi) (compact_summable_multivector_density_integrable xi) hT).
rewrite (measure_with_density_laws mu _ setT).
pose f:=real_total_integrand (fun x=>VN (value xi x)).
have hIntegral:is_measure_integral mu f (size xi)%:E:=
  @compact_summable_field_size_integral R UT V VN hVN mu hMu xi.
have hWhole:is_measure_subset_integral mu setT f (size xi)%:E.
  apply:(@measure_integral_graph_equivalent R UT mu f _ (size xi)%:E _ hIntegral).
  move=>x y;exact:iff_sym (partial_zero_extension_whole_graph _ _ x y).
exact:(measure_upper_integral_unique
  (measure_upper_integral_specification mu _ ) hWhole.2.1).
Qed.
End Density.
