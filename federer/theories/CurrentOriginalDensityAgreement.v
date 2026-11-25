(** Federer (1969), 4.1.8, p. 361: identify a
    normalized original density with the actual orienting
    field from its ball-limit definition. Reuse the
    bounded-density uniqueness and original orientation
    agreement already proved in 4.1.7, pp. 357–358. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading CurrentDomain CurrentSpaces
  CurrentCoefficientNorms CurrentMultivectorDual CurrentIntegrationCriterion NormalisedCurrentSealed
  CurrentOrientationSealed CurrentOrientationAlmost BoundedCurrentDensityUniqueness
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  PartialFunctionUP PartialFunctionBasic OpenFamilyTopologyMathcomp MeasurableFunctionUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic RadonMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentOriginalDensityAgreement.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation UT := (current_domain R n U).
Local Notation V := (exterior_power (R_n R n) m).
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Variable gamma:set UT->\bar R.
Variable xi:UT->V.
Hypothesis hRep:@is_current_integration_representation R h2 n m U hU T gamma xi.
Hypothesis hUnit:forall x,@current_vector_mass R h2 n m (xi x)<=1.
Hypothesis hVariation:@NormalisedCurrent.measure R h2 n m U hU T hT=gamma.
Local Notation theta := (@NormalisedCurrent.auxiliary_density R h2 n m U hU T hT).
Local Notation O := (@CurrentOrientation.value R h2 n m U hU T hT).

(** Source for [current_original_unit_density_agreement]:
    a unit-bounded original density with the original
    variation measure equals the original orienting field
    almost everywhere, supporting Federer 4.1.8, p. 361,
    through the uniqueness and ball formulas of 4.1.7. *)
Theorem current_original_unit_density_agreement:
  measure_almost_everywhere gamma [set x:UT|partial_function_graph O x (xi x)].
Proof.
have hNormal:=@NormalisedCurrent.laws R h2 n m U hU T hT.
have hBase:=normalised_distribution_representation_laws hNormal.
have hBound:=normalised_distribution_density_unit_bound hNormal.
have hOrientation:=@current_orientation_normalised_agreement R h2 n m U hU T hT.
rewrite hVariation in hBase hOrientation.
have hUnique:=@bounded_current_density_almost_unique R h2 n m U hU gamma
  (distribution_representation_measure hRep) (distribution_representation_radon hRep)
  xi theta (distribution_representation_weak_measurable hRep)
  (distribution_representation_weak_measurable hBase) hUnit hBound
  (@current_value R h2 n U hU m T)
  (distribution_representation_action hRep) (distribution_representation_action hBase).
apply:(@measure_almost_everywhere_mono R UT gamma (distribution_representation_measure hRep) _ _ _
  (measure_almost_everywhere_and (distribution_representation_measure hRep) hUnique hOrientation))
  =>x [hEq hGraph].
change (partial_function_graph O x (xi x)).
rewrite hEq;exact:hGraph.
Qed.
End CurrentOriginalDensityAgreement.
