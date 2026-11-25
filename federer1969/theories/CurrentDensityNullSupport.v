(** Federer (1969), 4.1.20, p. 378: the top-degree
    flat density current has zero action when its original
    support is Lebesgue null. This supporting Radon argument
    applies to every original density measure: variation is
    carried by current support, by 4.1.7, pp. 358–359, and
    is absolutely continuous with respect to that measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading CurrentDomain CurrentSpaces CurrentCoefficientNorms
  CurrentIntegrationCriterion OpenCurrentDensityUP OpenCurrentDensitySealed
  CurrentDensityVariation CurrentRadonSupport CurrentMassRepresentation
  CurrentMassSealed NormalisedCurrentSealed CurrentZeroMass
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  MeasureUP MeasureNullModification MeasureDensity MeasureDensityNullSets
  RadonMeasureUP SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section NullSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation UT:=(current_domain R n U).
Variable gamma:set UT->\bar R.
Hypothesis hGamma:is_measure gamma.
Hypothesis hRadon:is_radon_measure gamma.
Variable xi:UT->exterior_power X m.
Hypothesis hXi:@is_locally_integrable_open_current_density R h2 n m U gamma xi.
Local Notation T:=(@OpenCurrentDensity.value R h2 n m U hU
  gamma hGamma hRadon xi hXi).
Local Notation support:=(@current_support R h2 n U hU m T).
Local Notation S:=[set x:UT|support (set_val x)].

(** Source for [current_density_null_support]: the null-support
    step in Federer 4.1.20, p. 378, using the exact variation
    and its support from 4.1.7, pp. 358–359. Local summability
    suffices; no global finite mass is added. *)
Theorem current_density_null_support:gamma S=0->T=0.
Proof.
move=>hNull.
pose hT:=@current_open_density_representable R h2 n m U hU
  gamma hGamma hRadon xi hXi.
pose nu:=@NormalisedCurrent.measure R h2 n m U hU T hT.
have hBase:=normalised_distribution_representation_laws
  (@NormalisedCurrent.laws R h2 n m U hU T hT).
have hNu:is_measure nu:=distribution_representation_measure hBase.
have hSupport:nu S=0.
  rewrite /nu (@current_open_density_variation R h2 n m U hU
    gamma hGamma hRadon xi hXi hT).
  exact:(@measure_density_null_set R UT gamma _ hGamma _ S
    (measure_with_density_laws gamma _) hNull).
have hOutside:=@current_radon_outside_support_null R h2 n m U hU T hT.
have hTotal:nu setT=nu S.
  apply:(@measure_null_modification_value R UT nu hNu setT S
    [set x:UT|~support (set_val x)] hOutside)=>x hGood.
  split;last by [].
  move=>_;apply:contrapT=>hNo;exact:hGood hNo.
apply:(@current_zero_mass R h2 n m U hU T).
by rewrite (@current_represented_mass_total R h2 n m U hU T hT)
  -/nu hTotal hSupport.
Qed.
End NullSupport.
