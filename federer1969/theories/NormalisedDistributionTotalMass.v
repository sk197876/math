(** Federer (1969), 4.1.7, p. 358: the
    mass of a represented current is the
    total original variation measure. This supporting
    abstract-dual argument uses 4.1.5, p. 350,
    and the compact positive-test supremum of
    2.5.14, p. 107. Infinite masses remain
    in the original extended-real order. *)
From mathcomp Require Import all_boot functions all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP ContinuousDualUP RealFunctionalNormUP WeakEvaluationTopologyUP
  FunctionLatticeUP CompactSupportFunctionUP CompactOpenContentUP ExtendedSupremumUP ExtendedRealBoundsUP
  MeasureUP MeasureSplit RadonMeasureUP MeasureIntegralUP MeasureIntegralUniqueness
  SummableRealFunctionUP RealTotalCharacteristicBounds DistributionVariationUP
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  NormalisedDistributionScalarIntegral NormalisedScalarIntegralGauge RadonPositiveCompactOpenContent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section NormalisedDistributionTotalMass.
Variable R:realType.
Variable X:topologicalType.
Hypothesis hLocal:locally_compact (@setT X).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable D:lmodType R.
Variable ed:Hom D (Hom Y R^o).
Variable DN:D->R.
Hypothesis hD:is_continuous_dual hNY ed DN.
Variable O:set (set D).
Hypothesis hO:is_weak_evaluation_topology (fun a y=>ed a y) O.
Variable E:lmodType R.
Variable value:Hom E (GRing.Lmodule.clone R (X->Y) _).
Variable S:Hom E R^o.
Variable mu:set X->\bar R.
Variable k:X->D.
Hypothesis hRepresentation:is_normalised_distribution_representation hD hO value S mu k.
Let hBase:=normalised_distribution_representation_laws hRepresentation.
Let hm:=distribution_representation_measure hBase.
Let hr:=distribution_representation_radon hBase.
Local Notation F := (@normalised_distribution_scalar_integral R X Y NY hNY D ed DN hD O hO E value S mu k hRepresentation).
Local Notation hF := (@normalised_distribution_scalar_integral_laws R X Y NY hNY D ed DN hD O hO E value S mu k hRepresentation).

(** Source for [normalised_distribution_total_mass]:
    the original unit-majorant test supremum equals
    the total variation measure, supporting
    Federer 4.1.7, p. 358. The
    proof uses compact scalar tests below one,
    then their original Radon open-set supremum. *)
Theorem normalised_distribution_total_mass:
  is_distribution_variation_value NY value S (fun _=>1) (mu setT).
Proof.
constructor.
- move=>a [phi [hPhi <-]].
  have hAction:=distribution_representation_action hBase phi.
  have hBound:forall x:X,ed (k x) (value phi x)<=1.
    move=>x.
    have hDualNorm:=continuous_dual_norm_laws hD (k x).
    have hEval:=real_functional_norm_bound hDualNorm (value phi x).
    have hProduct:=ler_wpM2l (real_functional_norm_nonnegative hDualNorm) (hPhi x).
    rewrite mulr1 in hProduct.
    exact:le_trans (ler_norm _) (le_trans hEval
      (le_trans hProduct (normalised_distribution_density_unit_bound hRepresentation x))).
  have hUpper:=@real_total_integral_supported_upper_bound R X mu hm setT
    (fun x=>ed (k x) (value phi x)) (S phi)%:E 1
    (measure_measurable_whole hm) ltr01 hAction (fun x _=>hBound x)
    (fun x hx=>False_ind _ (hx Logic.I)).
  by rewrite mul1e in hUpper.
- move=>b hUpper.
  have hContent:=@radon_positive_compact_open_content R X mu hm hr F hLocal hF.
  apply:(extended_real_supremum_least (@hContent setT (@openT X)))=>a [f [hTest ->]].
  have hPositive:positive_function_lattice (@compactly_supported_continuous_functions R X) f.
    split;first exact:hTest.1.
    move=>x;exact:(andP (hTest.2.1 x)).1.
  have hGauge:=@normalised_scalar_integral_original_gauge R X Y NY hNY D ed DN hD O hO
    E value S mu k hRepresentation f hPositive.
  apply:(extended_supremum_least hGauge)=>r [phi [hPhi hR]].
  apply:hUpper;exists phi;split;last exact:hR.
  move=>x;exact:le_trans (hPhi x) (andP (hTest.2.1 x)).2.
Qed.
End NormalisedDistributionTotalMass.
