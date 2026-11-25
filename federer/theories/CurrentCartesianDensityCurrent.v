(** Federer (1969), 4.1.8, p. 361: identify the
    actual Radon-density current by the full original
    separated-test characterisation. This proof uses only
    the original factor integral actions, product integral
    factorisation and the actual coordinate measure bijection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading EuclideanCartesianMap
  CurrentDomain CurrentSpaces CurrentIntegrationCriterion CurrentMultivectorDual MultivectorDualSealed
  CurrentCartesianDomain CurrentCartesianDomainMapsSealed CurrentCartesianMeasureSealed CurrentCartesianMeasureRadon
  CurrentCartesianDensityMeasurable CurrentCartesianDensityTestPairing
  CurrentCartesianProductUP CurrentCartesianTestProductSealed CurrentDegreeTransport
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  DistributionIntegralFieldUP MeasureUP ProductMeasure MeasureIntegralUP MeasureIntegralUniqueness
  MeasureIntegralGraphEquivalence PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition
  SummableRealFunctionUP SummableRealArithmetic LatticeL1ApproximationLaws SeparatedProductIntegral MeasureBijectionIntegralTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianDensityCurrent.
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
Variable C:@current_space R h2 (m+n) AB hAB (i+j).
Hypothesis hC:@is_current_integration_representation R h2 (m+n) (i+j) AB hAB C lambda zeta.

(** Source for [current_cartesian_density_current_diagonal]:
    integrating the original product density gives exactly
    S(alpha)T(beta) on each diagonal separated test,
    supporting Federer 4.1.8, p. 361. *)
Lemma current_cartesian_density_current_diagonal a b:
  @current_value R h2 (m+n) AB hAB (i+j) C (Pure i j a b)=
    @current_value R h2 m A hA i S a*@current_value R h2 n B hB j T b.
Proof.
pose f x:=@MultivectorDual.evaluation R X i (xi x) (va i a (set_val x)).
pose g y:=@MultivectorDual.evaluation R Y j (eta y) (vb j b (set_val y)).
pose h z:=@MultivectorDual.evaluation R Z (i+j) (zeta z) (vc (i+j) (Pure i j a b) (set_val z)).
have hIS:=distribution_representation_action hBaseS a.
have hIT:=distribution_representation_action hBaseT b.
have hProduct:=@separated_product_integral R AT BT alpha beta hAlpha hBeta f g
  (@current_value R h2 m A hA i S a) (@current_value R h2 n B hB j T b) hIS hIT.
have hComposed:is_measure_integral mu (partial_function_precompose J (real_total_integrand h))
    (@current_value R h2 m A hA i S a*@current_value R h2 n B hB j T b)%:E.
  apply:(@measure_integral_graph_equivalent R PT mu _ _ _ _ hProduct)=>z v.
  change (partial_function_graph (real_total_integrand (fun z:AT*BT=>f z.1*g z.2)) z v <->
    partial_function_graph (real_total_integrand h) (J z) v).
  by rewrite !real_total_integrand_graph /h current_cartesian_density_test_pairing.
have hOnProduct:=(@measure_bijection_integral_iff R PT CT mu lambda hm J D hBij
  (real_total_integrand h) _).1 hComposed.
have hAction:=distribution_representation_action hC (Pure i j a b).
exact:(EFin_inj (measure_integral_unique hAction hOnProduct)).
Qed.

(** Source for [current_cartesian_density_current_off_diagonal]:
    the original product-density current is zero on every
    valid off-diagonal separated test, supporting Federer
    4.1.8, p. 361. *)
Lemma current_cartesian_density_current_off_diagonal k l (e:(k+l)%N=(i+j)%N)
    a b:k<>i ->
  @current_value R h2 (m+n) AB hAB (i+j) C
    (@current_test_degree_transport R h2 (m+n) AB hAB (k+l) (i+j) e (Pure k l a b))=0.
Proof.
move=>hki.
pose phi:=@current_test_degree_transport R h2 (m+n) AB hAB (k+l) (i+j) e (Pure k l a b).
pose h z:=@MultivectorDual.evaluation R Z (i+j) (zeta z) (vc (i+j) phi (set_val z)).
have hZero:=@real_total_zero_integral R PT mu hm.
have hComposed:is_measure_integral mu (partial_function_precompose J (real_total_integrand h)) (0:R)%:E.
  apply:(@measure_integral_graph_equivalent R PT mu _ _ _ _ hZero)=>z v.
  change (partial_function_graph (real_total_integrand (fun _:PT=>(0:R))) z v <->
    partial_function_graph (real_total_integrand h) (J z) v).
  by rewrite !real_total_integrand_graph /h /phi (@current_cartesian_density_test_off_diagonal R h2 m n i j A B hA hB
    xi eta k l e a b z hki).
have hOnProduct:=(@measure_bijection_integral_iff R PT CT mu lambda hm J D hBij
  (real_total_integrand h) _).1 hComposed.
have hAction:=distribution_representation_action hC phi.
exact:(EFin_inj (measure_integral_unique hAction hOnProduct)).
Qed.

(** Source for [current_cartesian_density_current_characterisation]:
    the original Radon-density representation satisfies both
    original product equations, supporting Federer 4.1.8,
    p. 361. Uniqueness identifies the actual product later. *)
Theorem current_cartesian_density_current_characterisation:
  @is_current_cartesian_product R h2 m n A B hA hB Pure i j S T C.
Proof.
split;first exact:current_cartesian_density_current_diagonal.
move=>k l e hki a b;exact:(@current_cartesian_density_current_off_diagonal k l e a b hki).
Qed.
End CurrentCartesianDensityCurrent.
