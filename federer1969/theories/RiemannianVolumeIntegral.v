(** Federer (1969), 3.2.46, p. 282: the printed
    volume integral on every original Lebesgue-measurable
    subset B of A. The sealed density retains exactly its
    original partial domain and the actual original rho
    Hausdorff measure occurs on the other side. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions RiemannianTensorUP RiemannianMetricCarrier
  RiemannianHausdorff RiemannianVolumeDensity RiemannianChartVolumeDensity
  RiemannianChartReference RiemannianReferencePushforward RiemannianChartVolumeIntegral
  RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionPrecomposition PartialZeroExtension PartialZeroExtensionLaws
  PartialZeroExtensionPrecomposition MeasureUP MeasureIntegralUP MeasureSubsetIntegral
  MeasureIntegralGraphEquivalence MeasureStepIntegralIdentification MeasurePushforward MeasureRestriction
  InjectivePushforwardIntegral RestrictedIntegralIdentity BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_2_46_volume]: H_rho^n(B) is
    the Lebesgue integral on B of sqrt(discr g), Federer
    3.2.46, p. 282. No boundedness or finite-mass premise;
    every natural dimension including zero is retained.
    Original completed Lebesgue measurability is sufficient. *)
Theorem federer_3_2_46_volume (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) (hp : 0<=n%:R :> R)
    (B : set (inner_metric_space (@euclidean_inner_productP R n))) :
  B `<=` A -> measure_measurable (@euclidean_lebesgue_measure R n) B ->
  is_measure_subset_integral (@euclidean_lebesgue_measure R n) B
    (partial_real_function_embed (riemannian_volume_density hg))
    (riemannian_hausdorff_measure hg n%:R hp
      ((fun x : riemannian_metric_space hg=>val x) @^-1` B)).
Proof.
move=> hBA hB.
pose E := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose M := [the choiceType of riemannian_metric_space hg].
pose phi := @riemannian_chart_reference R n A g hg.
pose v := fun x : M=>(val x : E).
pose S := v @^-1` B.
pose j := partial_real_function_embed (riemannian_volume_density hg).
pose w := partial_function_total (fun x : M=>
  ((riemannian_chart_volume_density hg x)%:E : extended_real_line R)).
pose F := partial_function_zero_extension (0 : extended_real_line R) B j.
have hPhi := @riemannian_chart_reference_is_measure R n A g hg.
have hS := @riemannian_reference_measurable_preimage R n A g hg B hB.
have hIntegral := @riemannian_chart_volume_integral R n A g hg hp S hS.
have hGraph x z : partial_function_graph (partial_function_precompose v j) x z <->
    partial_function_graph w x z.
  split.
  - move=> [r [hR hRz]].
    have hEq : r=riemannian_chart_volume_density hg x.
      exact: partial_function_single_valued hR
        (@riemannian_chart_volume_density_graph R n A g hg x).
    change ((riemannian_chart_volume_density hg x)%:E=z); by rewrite -hEq.
  - move=> hz; exists (riemannian_chart_volume_density hg x); split.
    + exact: riemannian_chart_volume_density_graph.
    + exact hz.
have hTransportIntegral : is_measure_integral phi (partial_function_precompose v F)
    (riemannian_hausdorff_measure hg n%:R hp S).
  apply: (measure_integral_graph_equivalent _ hIntegral)=> x z.
  rewrite (@partial_zero_extension_precompose_graph M E (extended_real_line R) v 0 B j x z).
  have hFirst := @partial_function_zero_extension_graph M (extended_real_line R) 0 S w x z.
  have hSecond := @partial_function_zero_extension_graph M (extended_real_line R) 0 S
    (partial_function_precompose v j) x z.
  split=> hz.
  - have [[hx hw]|[hx hz0]] := hFirst.1 hz.
    + apply: hSecond.2; left; split; first exact hx; exact: (hGraph x z).2 hw.
    + apply: hSecond.2; right; by split.
  - have [[hx hj]|[hx hz0]] := hSecond.1 hz.
    + apply: hFirst.2; left; split; first exact hx; exact: (hGraph x z).1 hj.
    + apply: hFirst.2; right; by split.
have hInj : injective v by move=> x y h; exact: val_inj h.
have hPushIntegral := (@injective_pushforward_integral_iff R M E phi hPhi v F hInj
  (riemannian_hausdorff_measure hg n%:R hp S)).1 hTransportIntegral.
rewrite (@riemannian_reference_pushforward R n A g hg) in hPushIntegral.
have hAMeas : measure_measurable (@euclidean_lebesgue_measure R n) A.
  exact (@borel_regular_borel_measurable R E (@euclidean_lebesgue_measure R n)
    (euclidean_lebesgue_is_measure R n) (euclidean_lebesgue_borel_regular R n) A
    (open_borel_set (@riemannian_chart_domain_open R n A g hg))).
have hAmbient := (@restricted_integral_zero_extension_iff R E (@euclidean_lebesgue_measure R n)
  (euclidean_lebesgue_is_measure R n) A F
  (riemannian_hausdorff_measure hg n%:R hp S) hAMeas).1 hPushIntegral.
have hIntersection : A `&` B=B.
  apply/seteqP; split=> x; first by move=> [_ hx].
  move=> hx; split; [exact: hBA x hx | exact hx].
apply: (measure_integral_graph_equivalent _ hAmbient)=> x z.
rewrite /F (partial_zero_extension_intersection_graph 0 A B j x z) hIntersection.
by [].
Qed.
