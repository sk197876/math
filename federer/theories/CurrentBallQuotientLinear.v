(** Federer (1969), 4.1.7, p. 357: linearity
    of the original characteristic-ball quotient in
    its constant covector. The actual L1 numerator
    uses the proved integral laws of 4.1.5,
    p. 350, on its original domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms CurrentCoefficientNorms
  CurrentCoefficientCompleteness CurrentDomain CurrentSpaces CurrentIntegrationCriterion
  NormalisedCurrentSealed CurrentOriginalBallFormula CurrentMultivectorDual MultivectorDualSealed
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionExtensionality PartialNormedArithmetic
  MeasureLpMembershipUP MeasureLpScaleMembership MeasureLpSumMembership
  MetricSubsetBackground MetricClosedBalls CharacteristicFunctionSealed
  DualLoneIntegralUP DualLoneIntegralSealed DualLoneIntegralAlgebra CurrentBallLimitsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentBallQuotientLinear.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation V := (exterior_power X m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation UT := (metric_subset (U:set (real_norm_metric_space hNX))).
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Local Notation mu := (@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation k := (@NormalisedCurrent.auxiliary_density R h2 n m U hU T hT).
Local Notation hRepresentation := (@NormalisedCurrent.laws R h2 n m U hU T hT).
Let hBase:=normalised_distribution_representation_laws hRepresentation.
Let hm:=distribution_representation_measure hBase.
Let hK:=distribution_representation_weak_measurable hBase.
Let hUnit:=normalised_distribution_density_unit_bound hRepresentation.
Local Notation I := (@current_representation_lone_integral R h2 n m U hU T mu k hRepresentation).
Local Notation ed := (@MultivectorDual.evaluation R X m).
Local Notation DN := (@current_vector_mass R h2 n m).
Local Notation hDual := (@current_multivector_continuous_dual R h2 n m).
Local Notation O := (@current_multivector_weak_opens R n m).
Local Notation hO := (@current_multivector_weak_laws R n m).
Local Notation F := (@current_ball_characteristic_field R h2 n m U).
Local Notation Q := (@is_current_ball_quotient R h2 n m U hU T hT).

(** Source for [current_ball_characteristic_linear]:
    the original b_(x,r)(c y+z) is
    c b_(x,r)y+b_(x,r)z on its full
    common domain, supporting Federer 4.1.7,
    p. 357. This is an equality of
    the actual partial-function graphs. *)
Lemma current_ball_characteristic_linear c y z x r:
  partial_vector_add (partial_vector_scale c (F y x r)) (F z x r)=F (c*:y+z) x r.
Proof.
apply:partial_function_graph_extensionality=>w a;split.
- move/partial_vector_add_graph=>[b [d [/partial_vector_scale_graph [v [hv hb]] [hd ha]]]].
  change ((@CharacteristicFunction.value R UT (metric_closed_ball x r) w)*:y=v) in hv.
  change ((@CharacteristicFunction.value R UT (metric_closed_ball x r) w)*:z=d) in hd.
  change ((@CharacteristicFunction.value R UT (metric_closed_ball x r) w)*:(c*:y+z)=a).
  rewrite ha hb -hv -hd scalerDr !scalerA.
  by rewrite [c*_]mulrC.
- move=>ha;apply/partial_vector_add_graph.
  exists (c*:((@CharacteristicFunction.value R UT (metric_closed_ball x r) w)*:y)),
    ((@CharacteristicFunction.value R UT (metric_closed_ball x r) w)*:z).
  split.
  + apply/partial_vector_scale_graph.
    exists ((@CharacteristicFunction.value R UT (metric_closed_ball x r) w)*:y);by split.
  + split;first by [].
    change ((@CharacteristicFunction.value R UT (metric_closed_ball x r) w)*:(c*:y+z)=a) in ha.
    rewrite -ha scalerDr !scalerA.
    by rewrite [c*_]mulrC.
Qed.

(** Source for [current_ball_quotient_linear]: the
    actual original ball quotient is linear in
    its constant covector wherever its two input
    quotients are defined, supporting Federer
    4.1.7, p. 357. The same positive
    finite ball mass is used throughout. *)
Theorem current_ball_quotient_linear c y z x r a b:
  Q y x r a->Q z x r b->Q (c*:y+z) x r (c*a+b).
Proof.
move=>[hr [mass [hMass [hPositive [hY hA]]]]]
  [hr' [mass' [hMass' [hPositive' [hZ hB]]]]].
have hMassEqual:mass=mass' by injection (eq_trans (esym hMass) hMass').
subst mass'.
have hScaled:=@measure_lp_function_scale R UT Y NY hNY mu hm 1 c (F y x r) hY.
have hCombined:=@measure_lp_function_add R UT Y NY hNY mu hm 1 _ (F z x r) hScaled hZ.
rewrite current_ball_characteristic_linear in hCombined.
split;first exact:hr.
exists mass;split;first exact:hMass.
split;first exact:hPositive.
split;first exact:hCombined.
have hIntegral:=@DualLoneIntegral.laws R UT Y NY hNY (@current_form_separable R h2 n m)
  V ed DN hDual O hO mu hm k hK hUnit.
have hLinear:=@dual_lone_integral_linear R UT Y NY hNY V ed k mu hm I hIntegral
  c (F y x r) (F z x r) hY hZ.
rewrite current_ball_characteristic_linear in hLinear.
by rewrite hA hB hLinear mulrDl -mulrA.
Qed.
End CurrentBallQuotientLinear.
