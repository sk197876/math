(** Federer (1969), 4.1.8, p. 361: apply the exact
    original density-variation identity of 4.1.7, p. 358,
    to an already specified current. The current is first
    identified with the actual canonical density current
    by its original all-test integral action. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading CurrentDomain CurrentSpaces
  CurrentCoefficientNorms CurrentIntegrationCriterion CurrentEvaluation
  OpenCurrentDensityUP OpenCurrentDensitySealed CurrentDensityVariation
  DistributionIntegrationRepresentationUP NormalisedCurrentSealed NormalisedDistributionRepresentationUP
  MeasureUP RadonMeasureUP MeasureDensity SummableRealFunctionUP MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentRepresentedDensityVariation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation UT := (current_domain R n U).
Local Notation V := (exterior_power (R_n R n) m).
Variable gamma:set UT->\bar R.
Hypothesis hGamma:is_measure gamma.
Hypothesis hRadon:is_radon_measure gamma.
Variable xi:UT->V.
Hypothesis hField:@is_locally_integrable_open_current_density R h2 n m U gamma xi.
Variable T:@current_space R h2 n U hU m.
Hypothesis hRep:@is_current_integration_representation R h2 n m U hU T gamma xi.
Local Notation W := (measure_with_density gamma (real_total_integrand (fun x=>@current_vector_mass R h2 n m (xi x)))).

(** Source for [current_represented_density_variation]: the
    exact original density formula for the variation of
    an arbitrary already represented current, supporting
    Federer 4.1.8, p. 361, by 4.1.7, p. 358. *)
Theorem current_represented_density_variation (nu:set UT->\bar R) (eta:UT->V):
  @is_normalised_current_representation R h2 n m U hU T nu eta ->nu=W.
Proof.
move=>hNormal.
pose C:=@OpenCurrentDensity.value R h2 n m U hU gamma hGamma hRadon xi hField.
have hC:=@OpenCurrentDensity.laws R h2 n m U hU gamma hGamma hRadon xi hField.
have hEqual:T=C.
  apply:(@current_values_extensional R h2 n m U hU)=>phi.
  exact:(EFin_inj (measure_integral_unique (distribution_representation_action hRep phi)
    (distribution_representation_action hC phi))).
rewrite hEqual in hNormal.
exact:(@current_density_exact_variation R h2 n m U hU gamma hGamma hRadon xi hField nu eta hNormal).
Qed.

(** Source for [current_represented_original_variation]: the
    opaque original scalar-test variation equals the measure
    weighted by the actual density mass, supporting Federer
    4.1.8, p. 361, by 4.1.7, p. 358. *)
Theorem current_represented_original_variation
    (hT:@is_integration_representable_current R h2 n m U hU T):
  @NormalisedCurrent.measure R h2 n m U hU T hT=W.
Proof.
exact:(current_represented_density_variation (@NormalisedCurrent.laws R h2 n m U hU T hT)).
Qed.
End CurrentRepresentedDensityVariation.
