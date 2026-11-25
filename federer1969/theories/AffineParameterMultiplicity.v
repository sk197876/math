(** Federer (1969), 2.10.16, p. 178, first affine formula: average the
    actual affine-slice count against the invariant measure of 2.7.16(7),
    pp. 140–141. Work with affine dimension d and codimension k=n-d, so the
    existing fibre and affine-measure interfaces require no vector-space
    casts. The final formula has degree k and k>0, the printed domain. Use
    any normalized Haar presentation from 2.7.16(6), p. 139; its projection
    orbit measure is the actual theta-star. Joint measurability, Fubini and
    pushforward integration prove the formula, rather than assuming an
    extended affine integral. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric FiniteCoordinates
  EuclideanProjectionSpace EuclideanProjectionMetric EuclideanOrthogonalInvariantMeasures
  OrthogonalInjectionSpaces OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  IsotropyGroupTopology LinearGroupTopology LinearGroupSealed HomogeneousSpaceUP HomogeneousSpaceLaws
  CompactGroupHaarNormalisation CompactGroupHomogeneousMeasures HaarIntegralUP
  OrthogonalProjectionProbability OrthogonalProjectionProbabilityUP
  AffineSubspaceSpace OrthogonalProjectionFibres AffineSubspaceParametrisation AffineSubspaceInvariantMeasure
  AffineSliceCount ProjectionJointMultiplicity ProjectionMultiplicityPrecomposition
  ProjectionMultiplicityIntegral IntegralGeometricMultiplicity IntegralGeometricMeasure ProjectionBeta
  EuclideanLebesgueDimensions TopologicalProductMaps
  ExtendedRealOrderTopology PartialFunctionBasic PartialProductSections PartialExtendedOrderLoci
  MeasureUP MeasureBasic MeasureSplit MeasurableFunctionUP MeasureAlmostUP MeasureAlmostBasic MeasurePushforward
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  MeasureNonnegativeIntegral PushforwardIntegral
  RadonMeasureUP RadonBorelRegularity BorelRegularMeasureUP TopologicalBorel
  ProductMeasure ProductFunctionFubini CountablyMeasurableUP CountablyMeasurableBasic
  CountablyMeasurableProduct CountablyMeasurableFunctions CountablyMeasurableNullModification
  ParameterizedIntegral MappingMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section AffineMultiplicity.
Variable R : realType.
Variables n d : nat.
Hypothesis hdn : (d<=n)%N.
Local Notation k := (n-d)%N.
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hBk := (@euclidean_inner_productP R k).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation hbk := (@coordinate_basisP R k).
Local Notation O := (euclidean_orthogonal_group R n).
Local Notation Ek := (inner_metric_space hBk).
Local Notation Pk := (orthogonal_projection_metric_space R n k).
Variables (mulO : O -> O -> O) (invO : O -> O) (eO : O).
Hypothesis hO : is_subgroup_restriction (linear_group_mul hBn hbn)
  (linear_group_inv hBn hbn) (linear_group_unit hBn hbn) O mulO invO eO.
Variable theta : set O -> \bar R.
Hypothesis htheta : is_normalised_haar_measure mulO theta.
Variable p : Pk.
Local Notation Ap := (orthogonal_projection_action hBk hBn hbn hO).
Local Notation q := (orbit_map Ap p).
Local Notation xi := (affine_parametrisation hdn p).
Local Notation mu := (@affine_product_measure R n d mulO theta htheta).
Local Notation gamma := (@affine_invariant_measure R n d hdn mulO p theta htheta).

(** Source for [affine_parameter_measure_is_measure]: supporting
    product measure theta_n times L^{n-d} in 2.10.16,
    p. 178, already used to define the actual affine measure
    in 2.7.16(7), p. 141. *)
Lemma affine_parameter_measure_is_measure : is_measure mu.
Proof. exact: product_measure_is_measure. Qed.

(** Source for [affine_parameter_measure_closed]: supporting
    closed-set measurability for the affine-parameter calculation
    in 2.10.16, p. 178. The existing Radon product law
    follows from the defining Haar representation; no new
    regularity hypothesis is imposed on the Borel set A. *)
Lemma affine_parameter_measure_closed (C : set (O*Ek)) :
  closed C -> measure_measurable mu C.
Proof.
move=> hC.
have [Theta [hT hmtheta hRep hReg]] := htheta.1.
have hr := @affine_product_measure_radon R n d mulO invO eO hO theta htheta Theta hT hRep.
apply: (borel_regular_borel_measurable affine_parameter_measure_is_measure
  (radon_borel_regular affine_parameter_measure_is_measure hr)).
exact: closed_borel_set hC.
Qed.

(** Source for [affine_parameter_projection_probability]: supporting
    orbit pushforward theta-star in 2.10.16, p. 178,
    exactly as in 2.7.16(6), p. 139. The projection
    probability is the existing sealed invariant measure. *)
Lemma affine_parameter_projection_probability :
  measure_pushforward q theta=@orthogonal_projection_probability R n k (leq_subr d n).
Proof.
have [phi [hphi huniq hall]] := @euclidean_theta_star_nm_exists_unique R n k
  mulO invO eO hO (leq_subr d n).
have hstar := @orthogonal_projection_probability_specification R n k (leq_subr d n)
  mulO invO eO hO.
have he := huniq _ hstar.
by rewrite (hall theta p htheta) -he.
Qed.

(** Source for [affine_parameter_count_measurable]: supporting
    actual parameter-count measurability for 2.10.16, p. 178.
    The continuous map (s,y) -> (y,p composed with s inverse)
    pulls back the Suslin incidence approximations of N. *)
Lemma affine_parameter_count_measurable
    (A : set (inner_metric_space hBn)) : borel_set A ->
  is_measure_measurable_function mu
    (partial_function_total (fun z : O*Ek => projection_joint_multiplicity A (z.2,q z.1))).
Proof.
move=> hA.
have hAP := orthogonal_projections_homogeneous hBk hbk hO.
have hq : continuous q := orbit_map_continuous hAP p.
have hu : continuous (fun z : O*Ek => (z.2,q z.1)).
  apply: topological_pair_continuous; first exact: second_projection_continuous.
  move=> z; exact: continuous_comp (@first_projection_continuous O Ek z) (hq z.1).
exact: (@projection_joint_precomposition_measurable R (O*Ek)%type n k mu
  (fun z => (z.2,q z.1)) A affine_parameter_measure_is_measure
  affine_parameter_measure_closed hu hA).
Qed.

(** Source for [affine_parameter_count_integral]: supporting
    parameter form of the first equality in 2.10.16, p. 178.
    Fubini produces the actual inner multiplicity integrals;
    the orbit pushforward and 2.10.15 identify their average
    with beta_1(n,n-d) I_1^{n-d}(A), including infinity. *)
Theorem affine_parameter_count_integral
    (A : set (inner_metric_space hBn)) : (0<k)%N -> borel_set A ->
  is_measure_integral mu
    (partial_function_total (fun z : O*Ek => projection_joint_multiplicity A (z.2,q z.1)))
    ((@projection_beta R n k (leq_subr d n) 1)%:E*
      @integral_geometric_measure R n k (leq_subr d n) 1 A).
Proof.
move=> hk hA.
pose f := partial_function_total (fun z : O*Ek => projection_joint_multiplicity A (z.2,q z.1)).
have hm := affine_parameter_measure_is_measure.
have hf := affine_parameter_count_measurable hA.
have hp : measure_almost_everywhere mu (partial_extended_nonnegative_locus f).
  apply: (@measure_almost_everywhere_mono R [the choiceType of ((O*Ek)%type)] mu hm
    setT _ _ (measure_almost_everywhere_true hm))=> z _.
  exists (projection_joint_multiplicity A (z.2,q z.1)); split=> //.
  exact: mapping_multiplicity_nonnegative.
have [hi _] := @nonnegative_measurable_function_integral R [the choiceType of ((O*Ek)%type)] mu hm f hf hp.
pose J := measure_lower_integral mu f.
have hwhole : measure_countably_measurable mu setT.
  apply: product_whole_countably_measurable; last exact: euclidean_lebesgue_countably_measurable.
  apply: finite_measurable_set_countably_measurable.
  - apply: measure_measurable_whole; by have [[Th [_ hmt _ _]] _] := htheta.
  - by rewrite htheta.2 ltry.
have hc : is_countably_measure_measurable_function mu (0 : extended_real_line R) f.
  exact: (@countably_measurable_function_on_countable_source R [the choiceType of ((O*Ek)%type)]
    (extended_real_line R) mu hm 0 f (@extended_real_zero_closed R) hwhole hf).
have hF := (@product_function_fubini R O Ek theta (@euclidean_lebesgue_measure R k)
  _ _ f J hi hc).1.
have hthetaJ : is_measure_integral theta
    (partial_function_total (fun s => projection_multiplicity_integral A (q s))) J.
  apply: (@measure_integral_graph_equivalent R O theta _ _ J _ hF)=> s z.
  rewrite parameterized_integral_specification.
  change (is_measure_integral (@euclidean_lebesgue_measure R k)
    (projection_multiplicity_integrand A (q s)) z <-> projection_multiplicity_integral A (q s)=z).
  have hsec := @projection_multiplicity_integral_specification R n k A (q s) hA.
  split; first by move=> hz; exact: esym (measure_integral_unique hz hsec).
  by move=> hz; rewrite -hz.
have hmtheta : is_measure theta by have [[Th [_ hmt _ _]] _] := htheta.
have hpush := (@measure_pushforward_integral_iff R O Pk theta hmtheta q
  (partial_function_total (projection_multiplicity_integral (m:=k) A)) hthetaJ.1 J).1 hthetaJ.
rewrite affine_parameter_projection_probability in hpush.
have hbook := (@federer_2_10_15 R n k (leq_subr d n) A hk hA).2.1.
have he := measure_integral_unique hpush hbook.
have hiJ : is_measure_integral mu f J := hi.
by rewrite he in hiJ.
Qed.

(** Source for [federer_2_10_16_affine]: direct first displayed
    affine-slice formula of 2.10.16, p. 178. The affine
    dimension is d, the book's measure degree is n-d>0,
    and gamma is the actual measure of 2.7.16(7), p. 141,
    representing its invariant integral. This does not claim
    the two further slicing identities later in 2.10.16. *)
Theorem federer_2_10_16_affine (A : set (inner_metric_space hBn)) :
  (0<k)%N -> borel_set A ->
  is_measure_integral gamma (partial_function_total (affine_slice_count (d:=d) A))
    ((@projection_beta R n k (leq_subr d n) 1)%:E*
      @integral_geometric_measure R n k (leq_subr d n) 1 A) /\
  @integral_geometric_measure R n k (leq_subr d n) 1 A=
    ((@projection_beta R n k (leq_subr d n) 1)^-1)%:E*
      measure_lower_integral gamma (partial_function_total (affine_slice_count (d:=d) A)).
Proof.
move=> hk hA.
have hi := affine_parameter_count_integral hk hA.
have hefun : (fun z : O*Ek => projection_joint_multiplicity A (z.2,q z.1))=
    (fun z => affine_slice_count A (xi z)).
  apply/funext=> [[s y]].
  rewrite (@affine_parametrisation_fibre R n d hdn mulO invO eO hO p s y).
  exact: esym (affine_slice_count_projection_fibre hdn A (q s) y).
rewrite hefun in hi.
have hiGamma := (@measure_pushforward_integral_iff R (O*Ek)%type
  (affine_subspace_space (@euclidean_inner_productP R d) hBn (@coordinate_basisP R d) hbn)
  mu affine_parameter_measure_is_measure xi (partial_function_total (affine_slice_count (d:=d) A))
  hi.1 _).1 hi.
split; first exact hiGamma.
have he := measure_lower_integral_unique (measure_lower_integral_specification _ _) hiGamma.2.2.
have hb := @projection_beta_positive R n k (leq_subr d n) 1 (lexx _).
have hne : @projection_beta R n k (leq_subr d n) 1!=0%R by rewrite gt_eqF.
by rewrite he muleA -EFinM mulVf // mul1e.
Qed.

End AffineMultiplicity.
