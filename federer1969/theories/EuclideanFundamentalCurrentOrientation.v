(** Federer (1969), 4.1.7, p. 358:
    the original maximal orientation of E^n
    is the coordinate top vector everywhere.
    The exact Lebesgue variation, positive finite
    mass of every original ball and constant
    scalar ball integrals prove every quotient
    limit, including at dimension zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct ExteriorGrading FiniteExteriorPowers
  AlternatingForms CurrentDomain CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentSpaces CurrentMultivectorDual
  MultivectorDualSealed CurrentIntegrationCriterion NormalisedCurrentSealed EuclideanFundamentalCurrent
  EuclideanFullDomainMeasure EuclideanFundamentalCurrentVariation AlmostConstantBallQuotient
  CurrentOriginalBallFormula CurrentBallLimitsUP CurrentOrientationSealed PositiveScalarGraphLimit
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP OpenFamilyTopologyMathcomp
  MetricSubsetBackground MetricClosedBalls CharacteristicFunctionSealed PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureLpMembershipUP DualLoneIntegralUP DualLoneIntegralSealed
  LoneCharacteristicBallQuotient SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section EuclideanFundamentalCurrentOrientation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation U := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation FT := (metric_subset (U:set (real_norm_metric_space hNX))).
Local Notation Y := (A_m X R^o n).
Local Notation NY := (@current_form_comass R h2 n n).
Local Notation hNY := (@current_form_comass_real_norm R h2 n n).
Local Notation D := (exterior_power X n).
Local Notation DN := (@current_vector_mass R h2 n n).
Local Notation ed := (@MultivectorDual.evaluation R X n).
Local Notation hDual := (@current_multivector_continuous_dual R h2 n n).
Local Notation O := (@current_multivector_weak_opens R n n).
Local Notation hO := (@current_multivector_weak_laws R n n).
Local Notation E := (@euclidean_fundamental_current R h2 n).
Local Notation top := (e_lambda (@coordinate_basis R n) (ord_tuple n)).
Variable hT:@is_integration_representable_current R h2 n n U hFull E.
Local Notation mu := (@NormalisedCurrent.measure R h2 n n U hFull E hT).
Local Notation k := (@NormalisedCurrent.auxiliary_density R h2 n n U hFull E hT).
Local Notation hR := (@NormalisedCurrent.laws R h2 n n U hFull E hT).
Let hBase:=normalised_distribution_representation_laws hR.
Let hm:=distribution_representation_measure hBase.
Let hr:=distribution_representation_radon hBase.
Local Notation I := (@current_representation_lone_integral R h2 n n U hFull E mu k hR).
Local Notation field := (@current_ball_characteristic_field R h2 n n U).
Local Notation P := (@CurrentOrientation.value R h2 n n U hFull E hT).

(** Source for [euclidean_fundamental_current_scalar_ball_limit]:
    every original scalar ball quotient of E^n
    has its constant limit at every point,
    supporting Federer 4.1.7, p. 358.
    Original characteristic functions, finite positive
    denominators and actual L1 numerators are retained. *)
Theorem euclidean_fundamental_current_scalar_ball_limit (x:FT) (y:Y):
  @is_current_ball_scalar_limit R h2 n n U hFull E hT y x (ed top y).
Proof.
have hAux:=@euclidean_fundamental_current_auxiliary_constant R h2 n hT.
have hAlmost:measure_almost_everywhere mu [set z:FT|ed (k z) y=ed top y].
  apply:(@measure_almost_everywhere_mono R FT mu hm _ _ _ hAux)=>z hz.
  exact:(congr1 (fun a:D=>ed a y) hz).
have hBalls:forall z:FT,forall r:R,0<r->exists b:R,mu (metric_closed_ball z r)=b%:E /\0<b.
  move=>z r hPositive.
  rewrite (@euclidean_fundamental_current_variation R h2 n hT).
  exact:(@euclidean_full_domain_ball_positive_finite R n z r hPositive).
have hLimit:=@almost_constant_ball_quotient_everywhere R FT mu hm hr
  (fun z=>ed (k z) y) (ed top y) hAlmost hBalls x.
have hI:=@DualLoneIntegral.laws R FT Y NY hNY (@current_form_separable R h2 n n)
  D ed DN hDual O hO mu hm k (distribution_representation_weak_measurable hBase)
  (normalised_distribution_density_unit_bound hR).
have hNumerator:=@lone_characteristic_ball_quotient R FT Y NY hNY D ed k mu hm hr I hI
  x y (ed top y) hLimit.
move=>epsilon hEpsilon.
have [d [hD hClose]]:=hNumerator epsilon hEpsilon.
exists d;split;first exact:hD.
move=>r hPositive hSmall.
have [b [hMass [hB [hMember hError]]]]:=hClose r hPositive hSmall.
exists (I (field y x r)/b);split;last exact:hError.
split;first exact:hPositive.
exists b;split;first exact:hMass.
split;first exact:hB.
split;[exact:hMember|by []].
Qed.

(** Source for [euclidean_fundamental_current_orientation_everywhere]:
    the original maximal orienting field of E^n
    is e_1 wedge ... wedge e_n at
    every original point, Federer 4.1.7,
    p. 358. The exact partial graph
    is used; no conull domain replaces it. *)
Theorem euclidean_fundamental_current_orientation_everywhere (x:FT):
  partial_function_graph P x top.
Proof.
apply:((@CurrentOrientation.laws R h2 n n U hFull E hT).2 x top).2=>y.
exact:(@euclidean_fundamental_current_scalar_ball_limit x y).
Qed.

(** Source for [euclidean_fundamental_current_orientation_graph]:
    the complete original orientation graph is
    the constant coordinate top vector, Federer
    4.1.7, p. 358. Both implications
    hold everywhere and in every dimension. *)
Theorem euclidean_fundamental_current_orientation_graph (x:FT) (a:D):
  partial_function_graph P x a<->a=top.
Proof.
split.
- move=>hA;exact:(partial_function_single_valued hA
    (@euclidean_fundamental_current_orientation_everywhere x)).
- move=>->;exact:euclidean_fundamental_current_orientation_everywhere.
Qed.

(** Source for [euclidean_fundamental_current_orientation_domain]:
    every point belongs to the original
    maximal orientation domain of E^n,
    supporting Federer 4.1.7, p. 358.
    No null exceptional set is removed. *)
Theorem euclidean_fundamental_current_orientation_domain:partial_function_domain P=setT.
Proof.
apply/seteqP;split;last by move=>x _;exists top;exact:euclidean_fundamental_current_orientation_everywhere.
by move=>x _.
Qed.
End EuclideanFundamentalCurrentOrientation.
