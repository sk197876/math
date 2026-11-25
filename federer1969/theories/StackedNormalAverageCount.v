(** Rotational double-normal count supporting Federer (1969), 2.10.16, p.
    178. Insert an independent ambient orthogonal rotation. Simultaneous
    left translation of the two Haar frame parameters leaves their product
    measure unchanged. For each fixed stacked map, the proved polar
    factorisation and determinant change give its rotational count; the
    unit-wedge average then gives the angular coefficient. This supplies a
    self-contained proof route in place of importing the generic-position
    argument in Federer, Dimension and measure (1947), §8, pp. 543–544. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric Hom
  EuclideanProjectionSpace EuclideanProjectionMetric EuclideanOrthogonalInvariantMeasures EuclideanLebesgueDimensions
  EuclideanLebesgueHaar OrthogonalGroupTopology OrthogonalGroupHaarMeasure OrthogonalInjectionSpaces
  IsotropyGroupTopology LinearGroupTopology LinearGroupSealed TopologicalGroupUP HomogeneousSpaceUP
  HomogeneousSpaceLaws CompactGroupHaarNormalisation OrthogonalProbabilityBackground AffineSubspaceInvariantMeasure
  StackedNormalFamily StackedNormalCounting EuclideanNormalJacobian StackedNormalPairIntegral
  LinearOrbitMultiplicityIntegral ProjectionBeta IntegralGeometricMeasure ContinuousFamilyMultiplicity
  CountableBorelProduct BorelRegularMeasureUP TopologicalBorel TopologicalProductMaps
  ExtendedRealOrderTopology PartialFunctionBasic MeasureUP MeasureBasic MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralGraphEquivalence MeasurableFunctionUP ProductMeasure ProductMeasureBijections
  MeasureBijectionUP MeasureBijectionLaws MeasureBijectionTotalIntegral HaarProbabilityTranslations
  TotalNonnegativeProductIntegral NonnegativeExtendedNormOrder RotatedProductIntegral MappingMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section AverageCount.
Variable R : realType.
Variables n a r : nat.
Hypotheses (hamn : (a+r<=n)%N) (hrna : (r<=n-a)%N).
Local Notation hnr := (leq_trans (leq_addl a r) hamn).
Local Notation O := (euclidean_orthogonal_group R n).
Local Notation P := (orthogonal_projection_metric_space R n a).
Local Notation Q := (orthogonal_projection_metric_space R n r).
Local Notation Y := [the metricType R of inner_metric_space (@euclidean_inner_productP R (a+r))].
Local Notation X := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Variables (mulO : O -> O -> O) (invO : O -> O) (eO : O).
Hypothesis hO : is_subgroup_restriction (linear_group_mul hBn hbn)
  (linear_group_inv hBn hbn) (linear_group_unit hBn hbn) O mulO invO eO.
Variable theta : set O -> \bar R.
Hypothesis htheta : is_normalised_haar_measure mulO theta.
Variable F : P*Q -> {linear R_n R n -> R_n R (a+r)}.
Hypothesis hF : is_stacked_normal_family F.
Local Notation ht := (@orthogonal_probability_is_measure R n mulO theta htheta).
Local Notation hpair := (product_measure_is_measure ht ht).
Local Notation hL := (@euclidean_lebesgue_is_measure R (a+r)).
Local Notation beta := (product_measure ht ht).
Local Notation mu := (product_measure hL hpair).
Local Notation Aa := (orthogonal_projection_action (@euclidean_inner_productP R a) hBn hbn hO).
Local Notation Ar := (orthogonal_projection_action (@euclidean_inner_productP R r) hBn hbn hO).

(** Source for [stacked_normal_average_count_integral]: supporting
    actual double-frame normal-coordinate integral for the
    middle formula of 2.10.16, p. 178. Its value is
    beta_1(n,a+r) I_1^{a+r}(A) times
    beta_1(n,r)/beta_1(n-a,r), with infinite values allowed. *)
Theorem stacked_normal_average_count_integral (p : P) (q : Q) (A : set X) :
  (0<r)%N -> borel_set A ->
  is_measure_integral mu
    (partial_function_total (fun z : Y*(O*O) =>
      (@mapping_multiplicity R X Y (F (Aa z.2.1 p,Ar z.2.2 q)) A z.1 : extended_real_line R)))
    (((@projection_beta R n (a+r) hamn 1)%:E*@integral_geometric_measure R n (a+r) hamn 1 A)*
      ((@projection_beta R n r hnr 1 / @projection_beta R (n-a) r hrna 1)%R)%:E).
Proof.
move=> hrpos hA.
pose P0 := euclidean_projection_space R n a.
pose Q0 := euclidean_projection_space R n r.
pose v (z : O*O) := (Aa z.1 p,Ar z.2 q).
pose e (z : (P*Q)*X) : Y := F z.1 z.2.
pose f (z : Y*(O*O)) : extended_real_line R := family_multiplicity (R:=R) e A (z.1,v z.2).
have hp z : 0<=f z by exact: mapping_multiplicity_nonnegative.
have hv := @normal_frame_pair_continuous R n a r mulO invO eO hO p q.
have hrt := @orthogonal_probability_borel_regular R n mulO invO eO hO theta htheta.
have hwt := @orthogonal_probability_whole_countably_measurable R n mulO theta htheta.
have hbO := @orthogonal_group_countable_base R n.
have [hbpair [hrpair hwpair]] := @countable_borel_product_background R O O theta theta ht ht hbO hbO hrt hrt hwt hwt.
have [hbmu [hrmu hwmu]] := @countable_borel_product_background R Y (O*O)%type
  (@euclidean_lebesgue_measure R (a+r)) beta hL hpair (euclidean_countable_open_base R (a+r)) hbpair
  (@euclidean_lebesgue_borel_regular R (a+r)) hrpair (euclidean_lebesgue_countably_measurable R (a+r)) hwpair.
pose hmu := product_measure_is_measure hL hpair.
have hclosed C : closed C -> measure_measurable mu C.
  move=> hC; exact (@borel_regular_borel_measurable R (Y*(O*O))%type mu hmu hrmu C (closed_borel_set hC)).
have hu : continuous (fun z : Y*(O*O) => (z.1,v z.2)).
  change (continuous (fun z : Y*(O*O) => (z.1,(v z.2 : P0*Q0)))).
  apply (@topological_pair_continuous (Y*(O*O))%type Y (P0*Q0)%type (@fst Y (O*O)%type) (fun z => v z.2));
    first exact: first_projection_continuous.
  move=> z; exact (continuous_comp (@second_projection_continuous Y (O*O)%type z) (hv z.2)).
have hfm := @stacked_normal_count_precomposition_measurable R n a r F (Y*(O*O))%type
  mu hmu (fun z => (z.1,v z.2)) A hF hu hA hclosed.
have hi := total_nonnegative_integral_specification hmu hp hfm.
pose I := measure_lower_integral mu (partial_function_total f).
have hI : 0<=I := @nonnegative_total_integral_value_ge0 R (Y*(O*O))%type mu hmu f I hp hi.
pose T := [the topologicalType of ((Y*(O*O))*O)%type].
pose nu := product_measure hmu ht.
pose hnu := product_measure_is_measure hmu ht.
have [_ [hrnu hwnu]] := @countable_borel_product_background R (Y*(O*O))%type O mu theta hmu ht
  hbmu hbO hrmu hrt hwmu hwt.
pose rot (z : T) := (mulO z.2 z.1.2.1,mulO z.2 z.1.2.2).
pose w (z : T) := (z.1.1,v (rot z)).
pose h (z : T) : extended_real_line R := family_multiplicity (R:=R) e A (w z).
have hT := lch_group_topological (orthogonal_group_lch hO).
have hrot : continuous rot.
  have hg : continuous (fun z : T => z.2) := @second_projection_continuous (Y*(O*O))%type O.
  have hst : continuous (fun z : T => z.1.2).
    move=> z; exact (continuous_comp (@first_projection_continuous (Y*(O*O))%type O z)
      (@second_projection_continuous Y (O*O)%type z.1)).
  have hs : continuous (fun z : T => z.1.2.1).
    move=> z; exact (continuous_comp (hst z) (@first_projection_continuous O O z.1.2)).
  have ht' : continuous (fun z : T => z.1.2.2).
    move=> z; exact (continuous_comp (hst z) (@second_projection_continuous O O z.1.2)).
  have hgs := @topological_pair_continuous T O O (fun z => z.2) (fun z => z.1.2.1) hg hs.
  have hgt := @topological_pair_continuous T O O (fun z => z.2) (fun z => z.1.2.2) hg ht'.
  apply (@topological_pair_continuous T O O (fun z => mulO z.2 z.1.2.1) (fun z => mulO z.2 z.1.2.2)).
  - move=> z; exact (continuous_comp (hgs z) (@topological_group_mul_continuous O mulO invO eO hT _)).
  - move=> z; exact (continuous_comp (hgt z) (@topological_group_mul_continuous O mulO invO eO hT _)).
have hw : continuous w.
  change (continuous (fun z : T => (z.1.1,(v (rot z) : P0*Q0)))).
  apply (@topological_pair_continuous T Y (P0*Q0)%type (fun z => z.1.1) (fun z => v (rot z))).
  - move=> z; exact (continuous_comp (@first_projection_continuous (Y*(O*O))%type O z)
      (@first_projection_continuous Y (O*O)%type z.1)).
  - move=> z; exact (continuous_comp (hrot z) (hv (rot z))).
have hclosednu C : closed C -> measure_measurable nu C.
  move=> hC; exact (@borel_regular_borel_measurable R T nu hnu hrnu C (closed_borel_set hC)).
have hhm := @stacked_normal_count_precomposition_measurable R n a r F T nu hnu w A hF hw hA hclosednu.
have hhs g : is_measure_integral mu (partial_function_total (fun z => h (z,g))) I.
  have hb := left_haar_translation_bijection hT htheta.1 g.
  have hpp := measure_bijection_product ht ht ht ht hb hb.
  have hbijmu := measure_bijection_product hL hpair hL hpair
    (measure_bijection_identity (@euclidean_lebesgue_measure R (a+r))) hpp.
  have hh := measure_bijection_total_nonnegative_integral hmu hmu hbijmu hp hi.
  apply: (@measure_integral_graph_equivalent R (Y*(O*O))%type mu _ _ I _ hh)=> -[y [s t]] z.
  by [].
have hAa := orthogonal_projections_homogeneous (@euclidean_inner_productP R a) (@coordinate_basisP R a) hO.
have hAr := orthogonal_projections_homogeneous (@euclidean_inner_productP R r) (@coordinate_basisP R r) hO.
pose B := (@projection_beta R n (a+r) hamn 1)%:E*@integral_geometric_measure R n (a+r) hamn 1 A.
have hB : 0<=B.
  apply: mule_ge0; first by rewrite lee_fin; exact: ltW (projection_beta_positive _ (lexx _)).
  exact (@measure_nonnegative R X _ (@integral_geometric_measure_is_measure R n (a+r) hamn 1 (lexx _)) A).
pose j (z : O*O) : extended_real_line R := (euclidean_normal_jacobian (F (v z)))%:E.
have hj z : 0<=j z by rewrite /j lee_fin; exact: euclidean_normal_jacobian_nonnegative.
have hrsec z : is_measure_integral (product_measure hL ht)
    (partial_function_total (fun yg : Y*O => h ((yg.1,z),yg.2))) (B*j z).
  have hmpos : (0<a+r)%N := leq_trans hrpos (leq_addl a r).
  have hlin := @linear_orthogonal_average_multiplicity_integral R n (a+r) hamn mulO invO eO hO
    theta htheta (F (v z)) A hmpos hA.
  rewrite [B*j z]muleC.
  apply: (@measure_integral_graph_equivalent R (Y*O)%type (product_measure hL ht) _ _ _ _ hlin)=> -[y g] b.
  have he : (fun x : X => F (v (rot ((y,z),g))) x)=
      (fun x => F (v z) (orthogonal_element_map (invO g) x)).
    apply/funext=> x; rewrite /v /rot /= (homogeneous_action_compatible hAa)
      (homogeneous_action_compatible hAr).
    exact (@stacked_normal_family_rotation R n a r mulO invO eO hO F hF _ _ g x).
  change (@mapping_multiplicity R X Y (fun x => F (v z) (orthogonal_element_map (invO g) x)) A y=b <->
    @mapping_multiplicity R X Y (fun x => F (v (rot ((y,z),g))) x) A y=b).
  by rewrite he.
have hjint := @stacked_normal_pair_integral R n a r hamn hrna mulO invO eO hO theta htheta F hF p q.
have heI := @rotated_product_integral_value R Y (O*O)%type O
  (@euclidean_lebesgue_measure R (a+r)) beta theta hL hpair ht h j I B _
  (euclidean_lebesgue_countably_measurable R (a+r)) hwpair hwt htheta.2 hI hB
  (fun z => @mapping_multiplicity_nonnegative R X Y (fun x => e ((w z).2,x)) A (w z).1) hj hhm hhs hrsec hjint.
have hiI : is_measure_integral mu (partial_function_total f) I := hi.
by rewrite heI in hiI.
Qed.
End AverageCount.
