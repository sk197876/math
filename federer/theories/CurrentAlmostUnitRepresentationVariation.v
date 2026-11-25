(** Federer (1969), 4.1.7, pp. 357–358, supporting the
    original-domain variation integrals in 4.1.13, pp. 369–370:
    a Radon representation with unit density almost everywhere
    has exactly the original variation measure. Almost-everywhere
    unit mass is retained; no pointwise unit representative is required. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  CurrentDomain CurrentSpaces CurrentCoefficientNorms CurrentIntegrationCriterion
  CurrentRepresentedDensityVariation NormalisedCurrentSealed OpenCurrentDensityUP
  DistributionIntegrationRepresentationUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  RadonMeasureUP RadonBorelRegularity BorelRegularMeasureUP MeasureDensityUP
  MeasureDensity MeasureDensityTransfer RealFiniteDensityIntegral SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentAlmostUnitRepresentationVariation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation UT := (current_domain R n U).
Local Notation E := (exterior_power (R_n R n) m).
Variable T:@current_space R h2 n U hU m.
Variable gamma:set UT->\bar R.
Variable xi:UT->E.
Hypothesis hRep:@is_current_integration_representation R h2 n m U hU T gamma xi.
Hypothesis hUnit:measure_almost_everywhere gamma
  [set x|@current_vector_mass R h2 n m (xi x)= 1].

(** Source for [current_almost_unit_representation_variation]:
    the exact original variation measure equals the supplied
    Radon measure when its representing density has unit
    mass almost everywhere, by Federer 4.1.7, pp. 357–358.
    This supports restriction of the original integrals in
    4.1.13, pp. 369–370, including empty domains and
    currents above the ambient dimension. *)
Theorem current_almost_unit_representation_variation
    (hT:@is_integration_representable_current R h2 n m U hU T):
  @NormalisedCurrent.measure R h2 n m U hU T hT=gamma.
Proof.
pose hm:=distribution_representation_measure hRep.
pose hr:=distribution_representation_radon hRep.
have hField:@is_locally_integrable_open_current_density R h2 n m U gamma xi.
  exact:conj (distribution_representation_weak_measurable hRep)
    (distribution_representation_compact_norm hRep).
have hVariation:=@current_represented_original_variation R h2 n m U hU
  gamma hm hr xi hField T hRep hT.
pose nu:=@NormalisedCurrent.measure R h2 n m U hU T hT.
pose H:=real_total_integrand (fun x:UT=>@current_vector_mass R h2 n m (xi x)).
have hDensity:is_measure_density gamma H nu.
  by rewrite /nu hVariation;exact:measure_with_density_laws.
have hEqual:measure_almost_equal gamma H (real_total_integrand (fun _:UT=>1)).
  apply:(@measure_almost_everywhere_mono R UT gamma hm _ _ _ hUnit)=>x hx.
  exists (1:R)%:E;split;rewrite real_total_integrand_graph;last by [].
  by rewrite hx.
have hOne:is_measure_density gamma (real_total_integrand (fun _:UT=>1)) nu.
  exact:(@measure_density_almost_equal R UT gamma nu hm H _ hDensity hEqual).
have hRegular:=borel_regular_is_regular hm (radon_borel_regular hm hr).
apply:funext=>A.
exact:(@regular_measure_unit_density_value R UT gamma nu hm hRegular hOne A).
Qed.
End CurrentAlmostUnitRepresentationVariation.
