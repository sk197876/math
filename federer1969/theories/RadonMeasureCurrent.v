(** Federer (1969), 4.1.7, p. 356:
    identify an original Radon measure on U
    with the zero-current obtained by restricting
    its associated Daniell integral to scalar tests. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms AlternatingZero AlternatingPairing
  CurrentDomain CurrentSpaces CurrentCoefficientNorms CurrentDiracDensity CurrentScalarUnitNorm
  CurrentMultivectorDual MultivectorDualSealed OpenCurrentDensityUP OpenCurrentDensitySealed CurrentIntegrationCriterion
  OpenFamilyTopologyMathcomp MeasurableTotalBasic PartialFunctionBasic SummableRealFunctionUP
  MeasureUP MeasureBasic RadonMeasureUP RadonBorelRegularity MeasureSubsetIntegral RealSubsetIntegralGraph
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureCharacteristicIntegral MeasureIntegralUP
  SmoothFunctionSpaceUP SmoothTestEvaluation DistributionVariationDomain DistributionIntegrationRepresentationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section RadonMeasureCurrent.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation UT := (current_domain R n U).
Local Notation unit := (@current_scalar_multivector_unit R n).
Variable gamma:set UT->\bar R.
Hypothesis hGamma:is_measure gamma.
Hypothesis hRadon:is_radon_measure gamma.

(** Source for [radon_current_unit_density_integrable]:
    the original scalar unit density is weakly
    measurable and locally mass-integrable for
    Radon gamma, supporting Federer 4.1.7,
    p. 356. Compact masses are finite by
    2.2.5, pp. 62–63. *)
Lemma radon_current_unit_density_integrable:
  @is_locally_integrable_open_current_density R h2 n 0%N U gamma (fun _=>unit).
Proof.
split.
- exact:(@measurable_total_constant R UT
    [the topologicalType of open_family_topological_space (@current_multivector_weak_laws R n 0%N).1]
    gamma hGamma unit).
- move=>K hK.
  have hKm:=radon_compact_measurable hGamma hRadon hK.
  have hFinite:gamma K \is a fin_num.
    rewrite ge0_fin_numE;first exact:(@radon_compact_finite R UT gamma hRadon K hK).
    exact:(@measure_nonnegative R UT gamma hGamma K).
  pose s:=@CharacteristicFunction.value R UT K.
  have hs:=@CharacteristicFunction.laws R UT K.
  have hChar:=@measure_characteristic_integral R UT gamma hGamma K s hs hKm.
  have hSubset:=(@real_subset_integral_total R UT gamma K (fun _=>1) s (gamma K)
    (fun x hx=>characteristic_on_set hs hx) (fun x hx=>characteristic_off_set hs hx)).2 hChar.
  have hMass:(fun _:UT=>@current_vector_mass R h2 n 0%N unit)=(fun _=>1).
    apply:funext=>x; exact:current_scalar_multivector_unit_mass.
  exists (fine (gamma K)); rewrite fineK // hMass; exact:hSubset.
Qed.

(** Source for [radon_measure_current]: the original
    measure gamma as an actual zero-current,
    Federer 4.1.7, p. 356. The value
    comes from the opaque original density-current
    interface, with unit scalar density. *)
Definition radon_measure_current:@current_space R h2 n U hU 0%N:=
  @OpenCurrentDensity.value R h2 n 0%N U hU gamma hGamma hRadon
    (fun _=>unit) radon_current_unit_density_integrable.

(** Source for [radon_measure_current_integral]: the
    exact original action is integration of the
    scalar coefficient of every zero-form test,
    Federer 4.1.7, p. 356. *)
Theorem radon_measure_current_integral psi:
  is_measure_integral gamma (real_total_integrand
    (fun x:UT=>zero_form_value (@current_test_value R h2 n U hU 0%N psi (set_val x))))
    (@current_value R h2 n U hU 0%N radon_measure_current psi)%:E.
Proof.
have hRepresentation:=@OpenCurrentDensity.laws R h2 n 0%N U hU gamma hGamma hRadon
  (fun _=>unit) radon_current_unit_density_integrable.
have hAction:=distribution_representation_action hRepresentation psi.
have hPoint:(fun x:UT=>@MultivectorDual.evaluation R X 0%N unit
    (@current_test_value R h2 n U hU 0%N psi (set_val x)))=
    (fun x:UT=>zero_form_value (@current_test_value R h2 n U hU 0%N psi (set_val x))).
  apply:funext=>x; rewrite MultivectorDual.laws.
  exact:current_scalar_multivector_unit_pairing.
by rewrite hPoint in hAction.
Qed.
End RadonMeasureCurrent.
