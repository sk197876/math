(** Federer (1969), 4.1.11, p. 365: the original sharp
    point-cone estimate. Specialize the preceding factorial
    join bound to the original unit point current. Preserve
    the printed wedge norm and the maximal partial orienting
    field of T, including infinite integral values. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ExtendedRealOrderTopology RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading ExteriorPowers ExteriorHomogeneousProducts CurrentDomain CurrentSpaces CurrentCoefficientNorms CurrentMassSealed
  CurrentIntegrationCriterion NormalisedCurrentSealed CurrentOrientationSealed CurrentDirac CurrentDiracDensity
  CurrentDiracRadonRepresentation CurrentDiracOrientation CurrentCompactElementaryPushforwards
  CurrentZeroDegreeExteriorLaws CurrentJoinSealed CurrentJoinSpatialWeight CurrentJoinMassCoefficient
  ScalarBetaCoefficient DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionPair PartialFunctionPostcomposition PartialProductSections PartialExtendedOrderLoci
  ParameterizedIntegral MeasurableFunctionUP MeasureUP ProductMeasure MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  MeasureNonnegativeLowerIntegral PointMassMeasure PointMassPartialIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentJoinConeMass.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n j:nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation XT := (current_domain R n Full).
Variable u:X.
Variable T:@current_space R h2 n Full hFull j.
Hypothesis hT:@is_integration_representable_current R h2 n j Full hFull T.
Local Notation D := (@dirac_current R h2 n Full hFull u).
Local Notation hD := (@current_dirac_representable R h2 n Full hFull u Logic.I).
Local Notation uD := (@current_dirac_domain_point R n Full u Logic.I).
Local Notation hDC := (@current_compact_dirac_support R h2 n Full hFull u Logic.I).
Local Notation unit := (@current_scalar_multivector_unit R n).
Local Notation OS := (@CurrentOrientation.value R h2 n 0%N Full hFull D hD).
Local Notation OT := (@CurrentOrientation.value R h2 n j Full hFull T hT).
Local Notation alpha := (@NormalisedCurrent.measure R h2 n 0%N Full hFull D hD).
Local Notation beta := (@NormalisedCurrent.measure R h2 n j Full hFull T hT).
Local Notation hBeta := (distribution_representation_measure
  (normalised_distribution_representation_laws (@NormalisedCurrent.laws R h2 n j Full hFull T hT))).
Local Notation N := (@current_vector_mass R h2 n (1+j)%N).
Local Notation G := (@current_join_spatial_weight R h2 n 0%N j D T hD hT).
Local Notation hAlpha := (distribution_representation_measure
  (normalised_distribution_representation_laws (@NormalisedCurrent.laws R h2 n 0%N Full hFull D hD))).
Local Notation Spatial := (measure_lower_integral (product_measure hAlpha hBeta) G).

(** Source for [current_join_cone_weight]: the original
    partial integrand |(y-u) wedge vec T(y)| in the
    cone mass estimate of Federer 4.1.11, p. 365.
    Its domain is exactly the original orientation domain. *)
Definition current_join_cone_weight:partial_function XT (extended_real_line R):=
  partial_function_postcompose
    (partial_function_pair (partial_function_total (fun y:XT=>y)) OT)
    (fun yb:XT*exterior_power X j=>
      (N (exterior_product (exterior_first_inclusion X (set_val yb.1-u)) yb.2))%:E).

(** Source for [current_join_cone_weight_graph]: the
    original cone weight has precisely its printed wedge
    norm wherever the original orientation is defined,
    supporting Federer 4.1.11, p. 365. *)
Lemma current_join_cone_weight_graph y v:
  partial_function_graph current_join_cone_weight y v<->
  exists b,partial_function_graph OT y b /\
    (N (exterior_product (exterior_first_inclusion X (set_val y-u)) b))%:E=v.
Proof.
split.
- move=>[[z b] [[hz hb] hValue]].
  have he:y=z:=hz;subst z;by exists b.
- move=>[b [hb hValue]];exists (y,b);split;[by split|exact:hValue].
Qed.

(** Source for [current_join_point_spatial_section]: at
    the original mass point the join's spatial weight is
    exactly the cone weight, supporting the specialization
    in Federer 4.1.11, p. 365. Scalar-unit multiplication
    supplies equality, without a triangle inequality. *)
Theorem current_join_point_spatial_section y v:
  partial_function_graph (partial_product_vertical_section G uD) y v<->
    partial_function_graph current_join_cone_weight y v.
Proof.
have hUnit:=@current_dirac_orientation_at_point R h2 n Full hFull u Logic.I hD.
change (partial_function_graph G (uD,y) v<->partial_function_graph current_join_cone_weight y v).
rewrite current_join_spatial_weight_graph current_join_cone_weight_graph;split.
- move=>[a [b [ha [hb hValue]]]].
  have he:a=unit:=partial_function_single_valued ha hUnit.
  subst a;exists b;split;first exact:hb.
  by rewrite /current_join_spatial_coefficient /current_scalar_multivector_unit
    exterior_product_zeroth_scalar_left scale1r in hValue.
- move=>[b [hb hValue]];exists unit,b;split;first exact:hUnit.
  split;first exact:hb.
  by rewrite /current_join_spatial_coefficient /current_scalar_multivector_unit
    exterior_product_zeroth_scalar_left scale1r.
Qed.

(** Source for [current_join_cone_weight_integral]: the
    literal original cone weight is integrable, and its
    integral equals the join's original spatial integral,
    supporting Federer 4.1.11, p. 365. The proof uses
    the preceding Fubini theorem on the actual point mass. *)
Theorem current_join_cone_weight_integral:
  is_measure_integral beta current_join_cone_weight Spatial.
Proof.
have hDouble:=@current_join_spatial_double_integral R h2 n 0%N j D T hD hT.
have hVariation:=@current_dirac_variation R h2 n Full hFull u Logic.I hD.
have hDomain:=measurable_function_domain hDouble.1.
rewrite hVariation in hDomain.
have[a hAtPoint]:=(@point_mass_almost_iff R XT uD _).1 hDomain.
have hSection:=(parameterized_integral_specification beta (partial_product_vertical_section G) uD a).1 hAtPoint.
have hCone:=@measure_integral_graph_equivalent R XT beta _ current_join_cone_weight a
  current_join_point_spatial_section hSection.
have hConeDomain:=measurable_function_domain hCone.1.
have hNonnegative:measure_almost_everywhere beta (partial_extended_nonnegative_locus current_join_cone_weight).
  apply:(@measure_almost_everywhere_mono R XT beta hBeta _ _ _ hConeDomain)=>y [v hv].
  have[b [hb hValue]]:=(current_join_cone_weight_graph y v).1 hv.
  exists v;split;first exact:hv.
  rewrite -hValue lee_fin;exact:real_seminorm_nonnegative (@current_vector_mass_real_norm R h2 n (1+j)%N).1 _.
have hNonnegativeValue:=@measure_lower_integral_nonnegative R XT beta hBeta current_join_cone_weight hNonnegative.
have hValue:=@measure_lower_integral_unique R XT beta current_join_cone_weight
  (measure_lower_integral beta current_join_cone_weight) a
  (measure_lower_integral_specification beta current_join_cone_weight) hCone.2.2.
rewrite hValue in hNonnegativeValue.
have hPointIntegral:=@point_mass_nonnegative_partial_integral R XT uD
  (parameterized_integral beta (partial_product_vertical_section G)) a hNonnegativeValue hAtPoint.
rewrite -hVariation in hPointIntegral.
have hSame:=measure_integral_unique hDouble hPointIntegral.
by rewrite -hSame in hCone.
Qed.

(** Source for [current_join_point_cone_mass_bound]: the
    mass of delta_u join T is at most 1/(j+1) times
    the literal original integral of |(y-u) wedge vec T(y)|,
    Federer 4.1.11, p. 365. Only T's original compact
    support and integration representation are required. *)
Theorem current_join_point_cone_mass_bound
    (hTC:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n Full hFull j T)):
  (@CurrentMass.value R h2 n (1+j)%N Full hFull
    (@CurrentJoin.value R h2 n 0%N j D T hDC hTC)<=
    ((j.+1%:R:R)^-1)%:E*measure_lower_integral beta current_join_cone_weight)%E.
Proof.
have hBound:=@current_join_factorial_mass_bound R h2 n 0%N j D T hD hT hDC hTC.
have hValue:=@measure_lower_integral_unique R XT beta current_join_cone_weight
  (measure_lower_integral beta current_join_cone_weight) Spatial
  (measure_lower_integral_specification beta current_join_cone_weight) current_join_cone_weight_integral.2.2.
by rewrite scalar_beta_coefficient_zero -hValue in hBound.
Qed.
End CurrentJoinConeMass.
