(** Federer (1969), 4.1.8, p. 361: original
    almost-everywhere product-density mass bounds. Transport
    the two original mass-one factor assertions through the
    original product measure and actual coordinate bijection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading EuclideanCartesianMap
  CurrentDomain CurrentSpaces CurrentIntegrationCriterion CurrentMultivectorDual MultivectorDualSealed
  CurrentCartesianDomain CurrentCartesianDomainMapsSealed CurrentCartesianMeasureSealed CurrentCartesianMeasureRadon
  CurrentCartesianDensityMeasurable CurrentCartesianDensityIntegrable CurrentCartesianDensityCurrent
  CurrentCartesianProductUnique CurrentCartesianProductSealed OpenCurrentDensityUP OpenCurrentDensitySealed
  RadonMeasureUP MeasureAlmostUP MeasureAlmostBasic CartesianMeasureAlmost
  CurrentCoefficientNorms CurrentCartesianVectorMassLower CurrentCartesianVectorSimpleMass
  CurrentCartesianDomainMapsLaws SimpleVectors
  CurrentCartesianProductUP CurrentCartesianTestProductSealed CurrentDegreeTransport
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  DistributionIntegralFieldUP MeasureUP ProductMeasure MeasureIntegralUP MeasureIntegralUniqueness
  MeasureIntegralGraphEquivalence PartialFunctionBasic PartialFunctionPrecomposition
  SummableRealFunctionUP SummableRealArithmetic SeparatedProductIntegral MeasureBijectionIntegralTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianDensityAlmost.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Variables (A:set X) (B:set Y).
Hypothesis hA:forall a,A a->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation AT := (current_domain R m A).
Local Notation BT := (current_domain R n B).
Local Notation CT := (current_domain R (m+n) AB).
Local Notation PT := (Choice.clone (AT*BT)%type _).
Local Notation J := (@CartesianCurrentDomain.join R m n A B).
Local Notation D := (@CartesianCurrentDomain.split R m n A B).
Local Notation Pure := (fun k l=>@CartesianTestProduct.value R h2 m n A B hA hB k l).
Local Notation va := (fun k=>@current_test_value R h2 m A hA k).
Local Notation vb := (fun k=>@current_test_value R h2 n B hB k).
Local Notation vc := (fun k=>@current_test_value R h2 (m+n) AB hAB k).
Variable S:@current_space R h2 m A hA i.
Variable T:@current_space R h2 n B hB j.
Variables (alpha:set AT->\bar R) (beta:set BT->\bar R).
Variables (xi:AT->exterior_power X i) (eta:BT->exterior_power Y j).
Hypothesis hS:@is_normalised_current_representation R h2 m i A hA S alpha xi.
Hypothesis hT:@is_normalised_current_representation R h2 n j B hB T beta eta.
Local Notation hBaseS := (normalised_distribution_representation_laws hS).
Local Notation hBaseT := (normalised_distribution_representation_laws hT).
Local Notation hAlpha := (distribution_representation_measure hBaseS).
Local Notation hBeta := (distribution_representation_measure hBaseT).
Local Notation mu := (product_measure hAlpha hBeta).
Local Notation hm := (product_measure_is_measure hAlpha hBeta).
Local Notation lambda := (@CartesianCurrentMeasure.value R m n A B alpha beta hAlpha hBeta).
Local Notation zeta := (@current_cartesian_density R m n i j A B xi eta).
Local Notation hBij := (@current_cartesian_measure_bijection R m n A B alpha beta hAlpha hBeta).


Local Notation DX := (fun z:CT=>(D z).1).
Local Notation DY := (fun z:CT=>(D z).2).
Local Notation NA := (@current_vector_mass R h2 m i).
Local Notation NB := (@current_vector_mass R h2 n j).
Local Notation NC := (@current_vector_mass R h2 (m+n) (i+j)).
Local Notation hLambda := (@current_cartesian_measure_is_measure R m n A B alpha beta hAlpha hBeta).

(** Source for [current_cartesian_factors_unit_almost]: both
    original normalized factor densities have mass one for
    almost every original product point, supporting Federer
    4.1.8, p. 361. Infinite factor masses are allowed. *)
Theorem current_cartesian_factors_unit_almost:
  measure_almost_everywhere lambda [set z:CT|NA (xi (DX z))= 1 /\NB (eta (DY z))= 1].
Proof.
have hFirst:=@product_almost_everywhere_first_factor R AT BT alpha beta hAlpha hBeta
  [set x|NA (xi x)= 1] (normalised_distribution_density_unit_norm hS).
have hSecond:=@product_almost_everywhere_second_factor R AT BT alpha beta hAlpha hBeta
  [set y|NB (eta y)= 1] (normalised_distribution_density_unit_norm hT).
apply:(@measure_bijection_almost_everywhere_iff R PT CT mu lambda J D hBij _).1.
apply:(@measure_almost_everywhere_mono R PT mu hm _ _ _
  (measure_almost_everywhere_and hm hFirst hSecond))=>z [hX hY].
change (NA (xi (D (J z)).1)= 1 /\NB (eta (D (J z)).2)= 1).
by rewrite current_cartesian_domain_join_split.
Qed.

(** Source for [current_cartesian_density_binomial_almost]:
    the original product coefficient times the printed
    binomial number has mass at least one almost everywhere,
    supporting Federer 4.1.8, p. 361. *)
Theorem current_cartesian_density_binomial_almost:
  measure_almost_everywhere lambda [set z:CT|1<='C(i+j,i)%:R*NC (zeta z)].
Proof.
apply:(@measure_almost_everywhere_mono R CT lambda hLambda _ _ _
  current_cartesian_factors_unit_almost)=>z [hX hY].
have h:=@current_cartesian_vector_mass_lower R h2 m n i j (xi (DX z)) (eta (DY z)).
by rewrite hX hY mul1r in h.
Qed.

(** Source for [current_cartesian_density_simple_unit_almost]:
    either simple original factor suffices at each product
    point; under that pointwise disjunction almost everywhere,
    the actual product density has mass one almost everywhere,
    supporting Federer 4.1.8, p. 361. *)
Theorem current_cartesian_density_simple_unit_almost:
  measure_almost_everywhere lambda [set z:CT|simple (xi (DX z)) \/simple (eta (DY z))] ->
  measure_almost_everywhere lambda [set z:CT|NC (zeta z)= 1].
Proof.
move=>hSimple.
apply:(@measure_almost_everywhere_mono R CT lambda hLambda _ _ _
  (measure_almost_everywhere_and hLambda current_cartesian_factors_unit_almost hSimple))
  =>z [[hX hY] hSimp].
have h:=@current_cartesian_vector_simple_mass R h2 m n i j (xi (DX z)) (eta (DY z)) hSimp.
by rewrite hX hY mul1r in h.
Qed.
End CurrentCartesianDensityAlmost.
