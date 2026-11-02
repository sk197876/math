(** Federer (1969), 3.2.26(3), p. 262: the actual
    projection multiplicity integral equals the subset integral
    of its approximate Jacobian. This is the constant-one
    case of 3.2.20, as corrected by the erratum p. 5,
    book p. 262 line 14. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanProjectionSpace EuclideanProjectionMetric EuclideanLebesgueDimensions EuclideanHausdorffLebesgue
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionPostcomposition
  PartialFunctionExtensionUP PartialFunctionExtensionality PartialMetricLipschitz PartialMetricLipschitzLaws
  PartialDensityProduct PartialZeroExtension ExtendedRealOrderTopology
  RectifiableSetUP RectifiableAreaFormula RectifiableAreaIntegrands RectifiableProjectionJacobian
  MeasureApproximateJacobian PartialMappingMultiplicity MappingMultiplicity ProjectionMultiplicityIntegral
  MeasureUP MeasureRestriction MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence
  HausdorffMeasure HausdorffClosedCoverAgreement LipschitzUP TopologicalBorel BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_zero_density_unit_source]: supporting
    constant-one source integrand in the application of
    3.2.20 to 3.2.26(3), p. 262. Multiplication
    by one preserves every actual Jacobian value; zero
    extension still takes place only outside the original
    source, without filling undefined values inside it. *)
Lemma partial_zero_density_unit_source (R:realType) (X Y:Type)
    (S:set X) (f:partial_function X Y) (J:partial_function X (extended_real_line R)):
  partial_function_domain f=S ->
  partial_function_zero_extension (0:extended_real_line R) S
    (partial_density_product (partial_function_postcompose f (fun _=>1)) J)=
    partial_function_zero_extension (0:extended_real_line R) S J.
Proof.
move=>hDomain; apply:partial_function_graph_extensionality=>x y.
have [hx|hx]:=pselect (S x).
- rewrite !(partial_function_zero_extension_on _ _ _ hx) partial_density_product_graph.
  split.
  + move=>[a [b [[z [hz hOne]] [hJ hProduct]]]].
    rewrite -hOne mul1e in hProduct; by rewrite -hProduct.
  + move=>hJ.
    have [z hz]:partial_function_domain f x by rewrite hDomain.
    exists 1,y; split; first by exists z.
    split; first exact hJ; exact:mul1e.
- by rewrite !(partial_function_zero_extension_off _ _ _ hx).
Qed.

(** Source for [projection_area_jacobian_integral]: the first
    equality g(p)=integral_S ap J_m p in 3.2.26(3),
    p. 262. Use the exact partial source graph and
    its actual fibre counting. The independently proved
    projection multiplicity integral supplies the target integral;
    3.2.20 supplies the source integral, without an extra
    measurability or integrability premise on the Jacobian. *)
Theorem projection_area_jacobian_integral (R:realType) m n
    (S:set (R_n R n)) (p:orthogonal_projection_metric_space R n m):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m S ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R n)) S ->
  is_measure_subset_integral (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) S
    (extended_measure_approximate_jacobian (measure_restrict
      (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) S) m m
      (partial_function_source_restrict S (partial_function_total (euclidean_projection_linear p))))
    (projection_multiplicity_integral S p).
Proof.
move=>hRect hS.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R m).
pose H:=@hausdorff_measure R X m.
pose F:=euclidean_projection_linear p.
pose f:=partial_function_source_restrict S (partial_function_total F).
have hH:=@hausdorff_measure_is_measure R X m.
have hSMeas:=borel_regular_borel_measurable hH (@hausdorff_measure_borel_regular R X m) hS.
have hDomain:partial_function_domain f=S.
  by rewrite /f partial_function_source_restrict_domain partial_function_total_domain setIT.
have hFull:@is_metric_lipschitz_bound R X Y setT F 1%R.
  split; first exact:ler01.
  move=>x y _ _; rewrite mul1r; exact:euclidean_projection_nonexpanding.
have hPartial:exists L,@is_partial_metric_lipschitz_bound R X Y f L.
  exists 1%R; apply:(@partial_total_restriction_lipschitz R X Y S F 1%R).2.
  split; first exact hFull.1; move=>x y _ _; exact:hFull.2 x y I I.
have hTargetMeasure:@hausdorff_measure R Y m=@euclidean_lebesgue_measure R m.
  apply:funext=>A; exact:(euclidean_hausdorff_spherical_lebesgue A).1.
have hExtension:is_partial_function_total_extension f F by move=>x y [_ hy].
have hMultiplicity y:@partial_mapping_multiplicity R (Choice.clone X _) Y f y=
    @mapping_multiplicity R (Choice.clone X _) (Choice.clone Y _) F S y.
  by rewrite (@partial_mapping_multiplicity_total_extension R (Choice.clone X _) Y f F y hExtension) hDomain.
have hTarget:rectifiable_area_target_integrand f (fun _=>1)=projection_multiplicity_integrand S p.
  apply:partial_function_graph_extensionality=>y z.
  change (1*@partial_mapping_multiplicity R (Choice.clone X _) Y f y=z <->
    @mapping_multiplicity R (Choice.clone X _) (Choice.clone Y _) F S y=z).
  by rewrite mul1e hMultiplicity.
have hTargetIntegral:=@projection_multiplicity_integral_specification R n m S p hS.
rewrite -hTargetMeasure -hTarget in hTargetIntegral.
have hSourceIntegral:=(@federer_3_2_20 R m n m S f (leqnn m) hRect hSMeas hDomain hPartial
  (fun _=>1) (projection_multiplicity_integral S p)).2 hTargetIntegral.
rewrite /rectifiable_area_source_integrand
  (partial_zero_density_unit_source _ hDomain) in hSourceIntegral.
exact hSourceIntegral.
Qed.
