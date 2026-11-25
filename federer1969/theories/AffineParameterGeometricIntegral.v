(** Parameter integral for the middle identity of Federer (1969), 2.10.16,
    p. 178. Put a=n-d and m=a+r. Double-count the two projection fibres, use
    the proved stacked-normal average, and divide by beta_1(n,r). The inner
    slice is measured by the ambient I_1^r, exactly as printed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanProjectionMetric EuclideanProjectionSpace EuclideanOrthogonalInvariantMeasures EuclideanLebesgueDimensions
  EuclideanLebesgueHaar EuclideanBlockCoordinates OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  OrthogonalInjectionSpaces IsotropyGroupTopology LinearGroupTopology LinearGroupSealed CompactGroupHaarNormalisation
  OrthogonalProbabilityBackground StackedNormalFamily StackedNormalAverageCount StackedNormalSliceParameters
  AffineGeometricSlice ProjectionBeta IntegralGeometricMeasure MappingMultiplicity TopologicalBorel
  ExtendedRealOrderTopology PartialFunctionBasic MeasureUP MeasureBasic MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness MeasureIntegralGraphEquivalence MeasureIntegralScaleLaw MeasureUpperIntegralScale
  MeasurableFunctionUP ProductMeasure ProductMeasureBijections MeasureBijectionUP MeasureBijectionTotalIntegral
  CountablyMeasurableUP CountablyMeasurableProduct TotalNonnegativeProductIntegral TotalNonnegativeExtendedScaleIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section ParameterSlices.
Variable R : realType.
Variables n d r : nat.
Hypothesis hdn : (d<=n)%N.
Local Notation a := (n-d)%N.
Hypotheses (hmn : (a+r<=n)%N) (hrna : (r<=n-a)%N).
Local Notation hrn := (leq_trans (leq_addl a r) hmn).
Local Notation O := (euclidean_orthogonal_group R n).
Local Notation P := (orthogonal_projection_metric_space R n a).
Local Notation Q := (orthogonal_projection_metric_space R n r).
Local Notation X := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
Local Notation Ea := [the metricType R of inner_metric_space (@euclidean_inner_productP R a)].
Local Notation Er := [the metricType R of inner_metric_space (@euclidean_inner_productP R r)].
Local Notation Em := [the metricType R of inner_metric_space (@euclidean_inner_productP R (a+r))].
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Variables (mulO : O -> O -> O) (invO : O -> O) (eO : O).
Hypothesis hO : is_subgroup_restriction (linear_group_mul hBn hbn)
  (linear_group_inv hBn hbn) (linear_group_unit hBn hbn) O mulO invO eO.
Variable theta : set O -> \bar R.
Hypothesis htheta : is_normalised_haar_measure mulO theta.
Local Notation ht := (@orthogonal_probability_is_measure R n mulO theta htheta).
Local Notation hLa := (@euclidean_lebesgue_is_measure R a).
Local Notation hLr := (@euclidean_lebesgue_is_measure R r).
Local Notation hLm := (@euclidean_lebesgue_is_measure R (a+r)).
Local Notation outer := (product_measure hLa ht).
Local Notation ho := (product_measure_is_measure hLa ht).
Local Notation inner := (product_measure hLr ht).
Local Notation hi := (product_measure_is_measure hLr ht).
Local Notation Aa := (orthogonal_projection_action (@euclidean_inner_productP R a) hBn hbn hO).
Local Notation Ar := (orthogonal_projection_action (@euclidean_inner_productP R r) hBn hbn hO).

(** Source for [affine_parameter_geometric_slice_integral]:
    supporting actual offset/frame integral for the
    middle formula of 2.10.16, p. 178. With m=n-d+r,
    its value is beta_1(n,m)/beta_1(d,r) times
    I_1^m(A); n-(n-d)=d is retained explicitly until
    the final affine-space statement. *)
Theorem affine_parameter_geometric_slice_integral (p : P) (q : Q) (A : set X) :
  (0<r)%N -> borel_set A ->
  is_measure_integral outer
    (partial_function_total (fun z : Ea*O =>
      (@integral_geometric_measure R n r hrn 1
        (A `&` [set x | euclidean_projection_linear (Aa z.2 p) x=z.1]) : extended_real_line R)))
    (((@projection_beta R n (a+r) hmn 1 / @projection_beta R (n-a) r hrna 1)%R)%:E*
      @integral_geometric_measure R n (a+r) hmn 1 A).
Proof.
move=> hrpos hA.
have [F hF] := @stacked_normal_family_exists R n a r.
have hstack := @stacked_normal_average_count_integral R n a r hmn hrna mulO invO eO hO
  theta htheta F hF p q A hrpos hA.
pose nu := product_measure hLm (product_measure_is_measure ht ht).
pose f (z : Em*(O*O)) : extended_real_line R :=
  @mapping_multiplicity R X Em (F (Aa z.2.1 p,Ar z.2.2 q)) A z.1.
have hpos z : 0<=f z by exact: mapping_multiplicity_nonnegative.
have hwt := @orthogonal_probability_whole_countably_measurable R n mulO theta htheta.
have hbij := @stacked_normal_slice_parameter_bijection R a r O theta ht hwt.
pose mu := product_measure ho hi.
pose hm := product_measure_is_measure ho hi.
pose S := [the choiceType of ((Ea*O)*(Er*O))%type].
pose fs (z : S) : extended_real_line R := @mapping_multiplicity R X Er
  (euclidean_projection_linear (Ar z.2.2 q))
  (A `&` [set x | euclidean_projection_linear (Aa z.1.2 p) x=z.1.1]) z.2.1.
have hboth := @measure_bijection_total_nonnegative_integral R S (Em*(O*O))%type mu nu hm
  (product_measure_is_measure hLm (product_measure_is_measure ht ht)) _ _ f _ hbij hpos hstack.
have hfs : is_measure_integral mu (partial_function_total fs)
    (((@projection_beta R n (a+r) hmn 1)%:E*@integral_geometric_measure R n (a+r) hmn 1 A)*
      ((@projection_beta R n r hrn 1 / @projection_beta R (n-a) r hrna 1)%R)%:E).
  apply: (@measure_integral_graph_equivalent R S mu _ _ _ _ hboth)=> -[[y s] [z t]] b.
  have he := @stacked_normal_slice_multiplicity R n a r F hF (Aa s p) (Ar t q) A y z.
  change (@mapping_multiplicity R X Em (F (Aa s p,Ar t q)) A (euclidean_block_join (y,z))=b <->
    @mapping_multiplicity R X Er (euclidean_projection_linear (Ar t q))
      (A `&` [set x | euclidean_projection_linear (Aa s p) x=y]) z=b).
  by rewrite he.
pose V (z : Ea*O) : extended_real_line R := @integral_geometric_measure R n r hrn 1
  (A `&` [set x | euclidean_projection_linear (Aa z.2 p) x=z.1]).
pose b := @projection_beta R n r hrn 1.
pose c := @projection_beta R (n-a) r hrna 1.
pose k := @projection_beta R n (a+r) hmn 1.
pose I := @integral_geometric_measure R n (a+r) hmn 1 A.
have hsec z : is_measure_integral inner (partial_function_total (fun yt => fs (z,yt))) (b%:E*V z).
  exact (@projection_haar_joint_multiplicity_integral R n r hrn mulO invO eO hO theta htheta q _ hrpos
    (euclidean_projection_slice_borel (Aa z.2 p) z.1 hA)).
have hwouter := @product_whole_countably_measurable R Ea O (@euclidean_lebesgue_measure R a) theta hLa ht
  (euclidean_lebesgue_countably_measurable R a) hwt.
have hwinner := @product_whole_countably_measurable R Er O (@euclidean_lebesgue_measure R r) theta hLr ht
  (euclidean_lebesgue_countably_measurable R r) hwt.
have hwmu := @product_whole_countably_measurable R (Ea*O)%type (Er*O)%type outer inner ho hi hwouter hwinner.
have hoV := @total_nonnegative_product_vertical_sections R (Ea*O)%type (Er*O)%type outer inner ho hi fs
  (fun z => b%:E*V z) hwmu (fun z => @mapping_multiplicity_nonnegative R X Er _ _ _) hfs.1 hsec.
have hedouble := measure_lower_integral_unique (measure_lower_integral_specification mu (partial_function_total fs)) hfs.2.2.
rewrite hedouble in hoV.
have hb : (0<b)%R := projection_beta_positive _ (lexx _).
have hbne : b!=0%R by rewrite gt_eqF.
have hi0 : 0<=((b^-1)%R)%:E by rewrite lee_fin invr_ge0; exact: ltW hb.
have hV z : 0<=V z := measure_nonnegative (@integral_geometric_measure_is_measure R n r hrn 1 (lexx _)) _.
have hbE : 0<=b%:E by rewrite lee_fin; exact: ltW hb.
have hs := @total_nonnegative_extended_scale_integral R (Ea*O)%type outer ho (fun z => b%:E*V z)
  ((k%:E*I)*(b/c)%R%:E) ((b^-1)%R)%:E (fun z => mule_ge0 hbE (hV z)) hoV hi0.
have hcanc z : ((b^-1)%R)%:E*(b%:E*V z)=V z by rewrite muleA -EFinM mulVf // mul1e.
have hvint : is_measure_integral outer (partial_function_total V)
    (((b^-1)%R)%:E*((k%:E*I)*(b/c)%R%:E)).
  apply: (@measure_integral_graph_equivalent R (Ea*O)%type outer _ _ _ _ hs)=> z y.
  change (((b^-1)%R)%:E*(b%:E*V z)=y <-> V z=y); by rewrite hcanc.
have hvalue : ((b^-1)%R)%:E*((k%:E*I)*(b/c)%R%:E)=(k/c)%R%:E*I.
  have he : (k%:E*I)*(b/c)%R%:E=(k*(b/c))%R%:E*I.
    by rewrite [LHS]muleC muleA -EFinM mulrC.
  rewrite he muleA -EFinM.
  have hk : (b^-1*(k*(b/c))=k/c)%R.
    by rewrite mulrCA [((b^-1)*(b*c^-1))%R]mulrA mulVf // mul1r.
  by rewrite hk.
by rewrite hvalue in hvint.
Qed.
End ParameterSlices.
