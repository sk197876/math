(** Federer (1969), 3.2.6, pp. 245–246: scalar
    target specialization of the first identity, used for
    the positive and negative derivative sets in the second
    identity. The coordinate adapter preserves the actual
    derivative domain and scalar Lebesgue normalization. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanOneCoordinate
  RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition
  PartialZeroExtension PartialDensityProduct RealCurveDerivativeIntegrands MappingMultiplicity
  MeasureUP MeasureIntegralUP MeasureIntegralGraphEquivalence MeasurePushforward LebesgueScalarMeasure CoveringFamilyUP
  LocallyAbsolutelyContinuousCurve EuclideanCurveAreaIntegrands AbsoluteContinuousCurveArea
  EuclideanScalarCurveEmbedding InjectivePushforwardIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [scalar_curve_area_source_integrand]: the
    n=1 source integrand (g composed with f)|f'| on A
    in Federer 3.2.6, p. 245, with actual partial f'. *)
Definition scalar_curve_area_source_integrand (R:realType) (f:R->R)
    (A:set (real_line_metric R)) (g:R->R):=
  partial_function_zero_extension (0:extended_real_line R) A
    (partial_density_product (partial_function_total (fun x=>(g (f x))%:E:extended_real_line R))
      (real_curve_absolute_derivative_integrand f)).

(** Source for [scalar_curve_area_target_integrand]: the
    n=1 target integrand g(y)N(f|A,y) in Federer
    3.2.6, p. 245, with actual scalar counting fibres. *)
Definition scalar_curve_area_target_integrand (R:realType) (f:R->R)
    (A:set (real_line_metric R)) (g:R->R):=
  partial_function_total (fun y=>((g y)%:E*
    @mapping_multiplicity R [the choiceType of real_line_metric R] R f A y:extended_real_line R)).

(** Source for [scalar_curve_area_source_embedding_graph]:
    supporting exact scalar integrand identification for the
    n=1 application in Federer 3.2.6, pp. 245–246. *)
Lemma scalar_curve_area_source_embedding_graph (R:realType) (f:R->R)
    (A:set (real_line_metric R)) (g:R->R) x z:
  partial_function_graph (curve_area_source_integrand (fun t=>euclidean_one_embed (f t)) A
    (fun y=>g (euclidean_one_project y))) x z <->
  partial_function_graph (scalar_curve_area_source_integrand f A g) x z.
Proof.
case:(pselect (A x))=>hx.
- rewrite /curve_area_source_integrand /scalar_curve_area_source_integrand
    !(partial_function_zero_extension_on _ _ _ hx).
  split=>h; have [r [s [hr [hs he]]]]:=(partial_density_product_graph _ _ x z).1 h;
    apply/partial_density_product_graph; exists r,s; split.
  + change ((g (euclidean_one_project (euclidean_one_embed (f x))))%:E=r) in hr.
    by rewrite euclidean_one_embedK in hr.
  + split=>//; exact ((euclidean_scalar_curve_speed_graph f x s).1 hs).
  + change ((g (euclidean_one_project (euclidean_one_embed (f x))))%:E=r).
    by rewrite euclidean_one_embedK.
  + split=>//; exact ((euclidean_scalar_curve_speed_graph f x s).2 hs).
- by rewrite /curve_area_source_integrand /scalar_curve_area_source_integrand
    !(partial_function_zero_extension_off _ _ _ hx).
Qed.

(** Source for [scalar_curve_area_target_embedding_graph]:
    supporting exact target integrand identification for the
    n=1 application in Federer 3.2.6, pp. 245–246. *)
Lemma scalar_curve_area_target_embedding_graph (R:realType) (f:R->R)
    (A:set (real_line_metric R)) (g:R->R) y z:
  partial_function_graph (partial_function_precompose (@euclidean_one_embed R)
    (curve_area_target_integrand (fun t=>euclidean_one_embed (f t)) A
      (fun x=>g (euclidean_one_project x)))) y z <->
  partial_function_graph (scalar_curve_area_target_integrand f A g) y z.
Proof.
change ((g (euclidean_one_project (euclidean_one_embed y)))%:E*
  @mapping_multiplicity R [the choiceType of real_line_metric R] (R_n R 1)
    (fun t=>euclidean_one_embed (f t)) A (euclidean_one_embed y)=z <->
  (g y)%:E*@mapping_multiplicity R [the choiceType of real_line_metric R] R f A y=z).
by rewrite euclidean_one_embedK euclidean_scalar_curve_multiplicity.
Qed.

(** Source for [federer_3_2_6_1_scalar]: the n=1 case
    of the first equation in Federer 3.2.6, p. 245,
    written on the scalar line rather than its one-coordinate
    Euclidean copy. No measurability of g is assumed. *)
Theorem federer_3_2_6_1_scalar (R:realType) (f:R->R)
    (A:set (real_line_metric R)) (g:R->real_line_metric R):
  is_locally_absolutely_continuous_curve (f:R->real_line_metric R) -> metric_set_bounded A ->
  measure_measurable (@lebesgue_scalar_measure R) A -> forall a,
  is_measure_integral (@lebesgue_scalar_measure R) (scalar_curve_area_source_integrand f A g) a <->
  is_measure_integral (@lebesgue_scalar_measure R) (scalar_curve_area_target_integrand f A g) a.
Proof.
move=>hAC hBound hA a.
pose fE:=fun t=>euclidean_one_embed (f t).
pose gE:=fun y:R_n R 1=>(g (euclidean_one_project y):real_line_metric R).
have hFirst:=federer_3_2_6_1 gE (euclidean_scalar_curve_absolute_continuity hAC) hBound hA a.
have hInj:injective (@euclidean_one_embed R):=can_inj (@euclidean_one_embedK R).
have hPush:=@injective_pushforward_integral_iff R [the choiceType of real_line_metric R]
  [the choiceType of inner_metric_space (@euclidean_inner_productP R 1)]
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) (@euclidean_one_embed R)
  (curve_area_target_integrand fE A gE) hInj a.
rewrite -(@euclidean_one_hausdorff_pushforward R) in hPush.
split=>hi.
- have hS:=measure_integral_graph_equivalent
    (fun x z=>iff_sym (scalar_curve_area_source_embedding_graph f A g x z)) hi.
  have hT:=hPush.2 (hFirst.1 hS).
  exact (measure_integral_graph_equivalent (scalar_curve_area_target_embedding_graph f A g) hT).
- have hT:=measure_integral_graph_equivalent
    (fun y z=>iff_sym (scalar_curve_area_target_embedding_graph f A g y z)) hi.
  have hS:=hFirst.2 (hPush.1 hT).
  exact (measure_integral_graph_equivalent (scalar_curve_area_source_embedding_graph f A g) hS).
Qed.
