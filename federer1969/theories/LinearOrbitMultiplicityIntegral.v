(** Supporting the affine slicing proof in Federer (1969), 2.10.16, p. 178:
    rotate a fixed linear map F from R^n to R^m and average its actual
    Lebesgue fibre count. A polar projection factorisation gives F=Kp; the
    proved determinant change handles K, including its singular case, and
    the existing projection orbit integral handles p. No measurable choice
    of polar factors is made: the map F is fixed during this argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanMetricCompleteness EuclideanMetricSeparability EuclideanLebesgueDimensions EuclideanLebesgueHaar
  EuclideanProjectionSpace EuclideanProjectionMetric EuclideanLinearMaps EuclideanOrthogonalInvariantMeasures
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure OrthogonalInjectionSpaces OrthogonalProbabilityBackground
  IsotropyGroupTopology LinearGroupTopology LinearGroupSealed CompactGroupHaarNormalisation
  HomogeneousSpaceUP HomogeneousSpaceLaws AffineSubspaceInvariantMeasure
  Hom InnerProductUP AdjointUP PolarFactorisationUP PolarProjection EuclideanNormalJacobian
  ProjectionOrbitMultiplicity ProjectionMultiplicityIntegral ProjectionBeta IntegralGeometricMeasure
  ContinuousFamilyIncidence ContinuousFamilyMultiplicity ContinuousFamilyPrecomposition
  ExtendedRealOrderTopology PartialFunctionBasic PartialExtendedOrderLoci PartialProductSections
  TopologicalBorel BorelClosedProjection BorelRegularMeasureUP TopologicalProductMaps
  MeasureUP MeasureBasic MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  MeasureIntegralGraphEquivalence MeasureNonnegativeIntegral MeasureAlmostUP MeasureAlmostBasic
  ProductMeasure ProductBorelRegularity ProductFunctionFubini CountablyMeasurableUP
  CountablyMeasurableProduct CountablyMeasurableFunctions CountablyMeasurableNullModification
  MappingMultiplicity LinearPostcompositionMultiplicity TotalNonnegativeExtendedScaleIntegral ParameterizedIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section LinearOrbit.
Variable R : realType.
Variables n m : nat.
Hypothesis hmn : (m<=n)%N.
Local Notation O := (euclidean_orthogonal_group R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hBm := (@euclidean_inner_productP R m).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation hbm := (@coordinate_basisP R m).
Local Notation X := [the metricType R of inner_metric_space hBn].
Local Notation Y := [the metricType R of inner_metric_space hBm].
Local Notation P := (orthogonal_projection_metric_space R n m).
Variables (mulO : O -> O -> O) (invO : O -> O) (eO : O).
Hypothesis hO : is_subgroup_restriction (linear_group_mul hBn hbn)
  (linear_group_inv hBn hbn) (linear_group_unit hBn hbn) O mulO invO eO.
Variable theta : set O -> \bar R.
Hypothesis htheta : is_normalised_haar_measure mulO theta.
Local Notation ht := (@orthogonal_probability_is_measure R n mulO theta htheta).
Local Notation nu := (product_measure (@euclidean_lebesgue_is_measure R m) ht).
Local Notation om := (@orthogonal_element_map R (R_n R n) _ hBn n _ hbn).
Local Notation Ap := (orthogonal_projection_action hBm hBn hbn hO).

(** Source for [linear_orthogonal_average_multiplicity_integral]:
    supporting fixed-map rotational average for the middle
    formula of 2.10.16, p. 178. The actual product
    integral is J(F) beta_1(n,m) I_1^m(A), with infinite
    values retained and singular maps contributing zero. *)
Theorem linear_orthogonal_average_multiplicity_integral
    (F : {linear R_n R n -> R_n R m}) (A : set X) :
  (0<m)%N -> borel_set A ->
  is_measure_integral nu
    (partial_function_total (fun z : Y*O =>
      (@mapping_multiplicity R X Y (fun x => F (om (invO z.2) x)) A z.1 : extended_real_line R)))
    ((euclidean_normal_jacobian F)%:E*
      ((@projection_beta R n m hmn 1)%:E*@integral_geometric_measure R n m hmn 1 A)).
Proof.
move=> hmpos hA.
have [K [p0 hfac]] := @polar_projection_factorisation_exists R (R_n R n) (R_n R m)
  _ _ hBn hBm n (@coordinate_basis R n) hbn m (@coordinate_basis R m) hbm hmn F.
pose p := orthogonal_projection_of hBm hBn hbn (projection_factor_orthogonal hfac).
pose q := orbit_map Ap p.
have hAP := orthogonal_projections_homogeneous hBm hbm hO.
have hq : continuous q := orbit_map_continuous hAP p.
have hQE g x : euclidean_projection_linear (q g) x=p0 (om (invO g) x).
  change (orthogonal_projection_map (Ap g p) x=p0 (om (invO g) x)).
  rewrite orthogonal_projection_actionE.
  by [].
have hFval g x : F (om (invO g) x)=K (euclidean_projection_linear (q g) x).
  by rewrite hQE (projection_factor_equation hfac).
pose ev (z : P*X) : Y := K (euclidean_projection_linear z.1 z.2).
have hev : continuous ev.
  change (continuous (fun z : euclidean_projection_space R n m * X =>
    (K (euclidean_projection_linear z.1 z.2) : Y))).
  move=> z; exact (continuous_comp (@euclidean_projection_evaluation_continuous R n m z)
    (@euclidean_linear_continuous R m K (euclidean_projection_linear z.1 z.2))).
pose u (z : Y*O) := (z.1,q z.2).
have hu : continuous u.
  apply (@topological_pair_continuous (Y*O)%type Y P (@fst Y O) (fun z => q z.2));
    first exact: first_projection_continuous.
  move=> z; exact (continuous_comp (@second_projection_continuous Y O z) (hq z.2)).
pose mu := nu.
pose hm := product_measure_is_measure (@euclidean_lebesgue_is_measure R m) ht.
have hrt := @orthogonal_probability_borel_regular R n mulO invO eO hO theta htheta.
have hwt := @orthogonal_probability_whole_countably_measurable R n mulO theta htheta.
have [U hU] := euclidean_countable_open_base R m.
have [V hV] := @orthogonal_group_countable_base R n.
have hreg := @product_measure_borel_regular R Y O (@euclidean_lebesgue_measure R m) theta
  (@euclidean_lebesgue_is_measure R m) ht U V hU hV (@euclidean_lebesgue_borel_regular R m) hrt.
have hc C : closed C -> measure_measurable mu C.
  move=> hC; exact (@borel_regular_borel_measurable R (Y*O)%type mu hm hreg C (closed_borel_set hC)).
have hnon : (@setT X)!=set0 by exists (0%R : X).
have hf := @continuous_family_multiplicity_precomposition_measurable R X P Y (Y*O)%type
  ev mu hm u A (@euclidean_metric_complete R n) (@orthogonal_projection_metric_complete R n m)
  (euclidean_metric_separable R n) (orthogonal_projection_metric_separable R n m) hnon
  (@metric_hausdorff R Y) hev hu (metric_borel_suslin hA) hc.
pose f := partial_function_total (fun z : Y*O => family_multiplicity (R:=R) ev A (u z)).
have hp : measure_almost_everywhere mu (partial_extended_nonnegative_locus f).
  apply: (@measure_almost_everywhere_mono R (Y*O)%type mu hm setT _ _ (measure_almost_everywhere_true hm))=> z _.
  exists (family_multiplicity (R:=R) ev A (u z)); split=> //.
  exact: mapping_multiplicity_nonnegative.
have [hi _] := @nonnegative_measurable_function_integral R (Y*O)%type mu hm f hf hp.
pose J := measure_lower_integral mu f.
have hw : measure_countably_measurable mu setT.
  exact (@product_whole_countably_measurable R Y O (@euclidean_lebesgue_measure R m) theta
    (@euclidean_lebesgue_is_measure R m) ht (euclidean_lebesgue_countably_measurable R m) hwt).
have hcount : is_countably_measure_measurable_function mu (0 : extended_real_line R) f.
  exact: (@countably_measurable_function_on_countable_source R (Y*O)%type (extended_real_line R)
    mu hm 0 f (@extended_real_zero_closed R) hw hf).
have ho := (@product_function_fubini R Y O (@euclidean_lebesgue_measure R m) theta
  (@euclidean_lebesgue_is_measure R m) ht f J hi hcount).2.
pose v g : extended_real_line R := (`|euclidean_det K|)%R%:E*projection_multiplicity_integral A (q g).
have hsec g : is_measure_integral (@euclidean_lebesgue_measure R m)
    (projection_multiplicity_integrand A (q g)) (projection_multiplicity_integral A (q g)).
  exact: projection_multiplicity_integral_specification hA.
have hKsec g := @linear_postcomposition_multiplicity_integral R X m (euclidean_projection_linear (q g)) K A
  (projection_multiplicity_integral A (q g)) (@euclidean_metric_complete R n)
  (euclidean_metric_separable R n) (@euclidean_projection_continuous R n m (q g)) hA (hsec g).
have hiv : is_measure_integral theta (partial_function_total v) J.
  apply: (@measure_integral_graph_equivalent R O theta _ _ J _ ho)=> g z.
  rewrite parameterized_integral_specification.
  change (is_measure_integral (@euclidean_lebesgue_measure R m)
    (partial_function_total (fun y => (@mapping_multiplicity R X Y
      (fun x => K (euclidean_projection_linear (q g) x)) A y : extended_real_line R))) z <-> v g=z).
  split; first by move=> hz; exact: esym (measure_integral_unique hz (hKsec g)).
  by move=> <-; exact: hKsec.
have hbase := @projection_orbit_multiplicity_integral R n m hmn mulO invO eO hO theta htheta A p hmpos hA.
have hdet : 0 <= (`|euclidean_det K|)%R%:E by rewrite lee_fin; exact: normr_ge0.
have hscaled := @total_nonnegative_extended_scale_integral R O theta ht
  (fun g => projection_multiplicity_integral A (q g))
  ((@projection_beta R n m hmn 1)%:E*@integral_geometric_measure R n m hmn 1 A)
  (`|euclidean_det K|)%R%:E
  (fun g => projection_multiplicity_integral_nonnegative (q g) hA) hbase
  hdet.
have heJ := measure_integral_unique hiv hscaled.
have hiJ : is_measure_integral mu f J := hi.
rewrite heJ -(projection_factor_normal_jacobian hfac) in hiJ.
apply: (@measure_integral_graph_equivalent R (Y*O)%type mu _ _ _ _ hiJ)=> -[y g] z.
have he : (fun x : X => K (euclidean_projection_linear (q g) x))=
    (fun x => F (om (invO g) x)).
  apply/funext=> x; exact: esym (hFval g x).
change (@mapping_multiplicity R X Y (fun x => K (euclidean_projection_linear (q g) x)) A y=z <->
  @mapping_multiplicity R X Y (fun x => F (om (invO g) x)) A y=z).
by rewrite he.
Qed.
End LinearOrbit.
