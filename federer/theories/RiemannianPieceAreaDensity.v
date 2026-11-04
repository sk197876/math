(** Federer (1969), 3.2.46, p. 282: the frozen-L
    localization of the area formula. This supporting theorem
    treats actual Lipschitz maps injective on Borel pieces and
    arbitrary source subsets, proving the target-metric image
    mass equals the actual varying-Jacobian density measure.
    General multiplicities and signed weights are later steps. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanMetricCompleteness EuclideanMetricSeparability EuclideanLebesgueDimensions
  LipschitzUP NormMetricScaleContinuity MetricSubsetBackground
  RiemannianTensorUP RiemannianTensorLocalComparison RiemannianMetricCarrier
  RiemannianChartLift RiemannianChartEllipsoid RiemannianHausdorff
  RiemannianLocalHausdorffComparison RiemannianLinearJacobian RiemannianTargetJacobian
  PositiveSymmetricNormFactor EuclideanLinearRealNull RealPower
  RealHausdorffMeasure RealPowerNaturalHausdorff EuclideanPieceAreaDensity
  JacobianDensityMeasure EuclideanJacobianMeasurable HausdorffMeasure RiemannianFrozenJacobianDensity
  MeasureUP MeasureBasic MeasureRestriction MeasureImagePullback MeasurePieceImagePullback MeasureDensityUP MeasureDensity
  BorelRegularMeasureUP TopologicalBorel BorelFamilyBasic InjectiveBorelImage
  CountableOpenBaseUP SeparableMetricBaseSealed MeasureLocalGeometricSqueeze.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_piece_area_density]: the actual
    image costs H_rho^m(f(E intersect S)) equal the actual
    varying-target Jacobian measure of E intersect S,
    supporting the countable univalent-piece procedure in
    3.2.46, p. 282. The original Borel piece E is
    retained; f need be injective only on E. No global
    injective extension, rank or area identity is assumed.
    Arbitrary outer S and infinite masses are retained.
    Local Euclidean Lipschitz reduction and general signed
    multiplicities remain later steps of the full formula. *)
Theorem riemannian_piece_area_density (R : realType) m n A h
    (hh : @is_continuous_riemannian_tensor R n A h)
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n))
    (hf : forall x, A (f x)) (hp : 0<=m%:R :> R) (E0 : set (R_n R m)) :
  is_metric_lipschitz setT f ->
  @borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] E0 ->
  {in E0 &, injective f} ->
  measure_restrict (measure_image_pullback (@riemannian_chart_lift R _ n A h hh f hf)
    (riemannian_hausdorff_measure hh m%:R hp)) E0 =
  measure_restrict (measure_with_density (@euclidean_lebesgue_measure R m)
    (@extended_target_riemannian_jacobian R m n A h hh f hf m)) E0.
Proof.
move=> hLip hE0 hInj.
pose X := [the metricType R of inner_metric_space (@euclidean_inner_productP R m)].
pose E := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose M := [the metricType R of riemannian_metric_space hh].
pose F := @riemannian_chart_lift R X n A h hh f hf.
pose beta := riemannian_hausdorff_measure hh m%:R hp.
pose mu := measure_restrict (measure_image_pullback F beta) E0.
pose J := @extended_target_riemannian_jacobian R m n A h hh f hf m.
pose phi := @euclidean_lebesgue_measure R m.
pose nu := measure_restrict (measure_with_density phi J) E0.
have hPhi := euclidean_lebesgue_is_measure R m.
have hBeta := @riemannian_hausdorff_is_measure R n A h hh m%:R hp.
have hMu := measure_restrict_is_measure (@measure_image_pullback_is_measure R X M F beta hBeta) E0.
have hPositive := @target_riemannian_jacobian_nonnegative_almost R m n A h hh f hf m hLip.
have hNu := measure_restrict_is_measure (measure_with_density_is_measure hPhi hPositive) E0.
have hCont : continuous f.
  have [K [hK hBound]] := hLip.
  apply: (@metric_fixed_lipschitz_continuous R X E f K (ltW hK)).
  by move=> x y; exact: hBound.2 x y Logic.I Logic.I.
have hFCont := @riemannian_chart_lift_continuous R X n A h hh f hf hCont.
have hFInj : {in E0 &, injective F}.
  move=> x y hx hy hEq; have hEqV := congr1 (fun z : M=>val z) hEq.
  exact (hInj _ _ hx hy hEqV).
have hBorel B (hB : @borel_set X B) : measure_measurable mu B /\ measure_measurable nu B.
  split.
  - apply: (@measure_piece_image_measurable R X M F beta E0 B hFInj).
    have hEB : @borel_set X (E0 `&` B).
      exact (@borel_family_binary_intersection X setT (@borel_set X) (borel_sets_family X) E0 B hE0 hB).
    have hImage : @borel_set M (F @` (E0 `&` B)).
      apply: (@injective_borel_image_borel R X M F (E0 `&` B)
        (@euclidean_metric_complete R m) (@euclidean_metric_separable R m)
        (@metric_hausdorff R M) hFCont hEB).
      move=> x y hx hy hEq; exact (hFInj _ _ (mem_set hx.1) (mem_set hy.1) hEq).
    exact (@borel_regular_borel_measurable R M beta hBeta
      (@riemannian_hausdorff_borel_regular R n A h hh m%:R hp) (F @` (E0 `&` B)) hImage).
  - apply: measure_restrict_measurable.
    apply: (@measure_with_density_measurable R X phi hPhi J B hPositive).
    exact (@borel_regular_borel_measurable R X phi hPhi
      (euclidean_lebesgue_borel_regular R m) B hB).
have [D [hCount hDense]] := euclidean_metric_separable R m.
pose U := @SeparableMetricBase.value R X D hCount hDense.
have hBase := @SeparableMetricBase.laws R X D hCount hDense.
have hLocal (lambda : R) (hLambda : 1<lambda) (a : X) :
    exists V : set X, open V /\ V a /\ forall S, S `<=` V ->
      (mu S<=(lambda^+(m+m))%:E*nu S)%E /\
      (nu S<=(lambda^+(m+m))%:E*mu S)%E.
  have hLambda0 : 0<lambda := lt_trans ltr01 hLambda.
  have hLambdaNe : lambda!=0 := lt0r_neq0 hLambda0.
  have [L [r [hr [hL [hPatch hHausdorff]]]]] :=
    @riemannian_local_hausdorff_comparison R n A h hh (f a) (hf a) lambda hLambda.
  have [T [d [hd [hT hTensor]]]] :=
    @riemannian_tensor_local_comparison R n A h hh (f a) (hf a) lambda hLambda.
  pose W : set M := [set z |
    inner_norm (@euclidean_inner_productP R n) (L (val z-f a))<r /\
    inner_norm (@euclidean_inner_productP R n) (T (val z-f a))<d].
  have hW : open W.
    apply: openI; exact: riemannian_chart_ellipsoid_open.
  pose V := F @^-1` W.
  have hV : open V := @open_comp X M F W (fun x _=>hFCont x) hW.
  exists V; split; first exact hV; split.
  - change (is_true (inner_norm (@euclidean_inner_productP R n) (L (f a-f a))<r) /\
      is_true (inner_norm (@euclidean_inner_productP R n) (T (f a-f a))<d)).
    by rewrite subrr !linear0 !inner_norm0.
  - move=> S hS.
    pose B0 := E0 `&` S.
    have hNearL x (hx : B0 x) : inner_norm (@euclidean_inner_productP R n) (L (f x-f a))<=r.
      exact: ltW (hS x hx.2).1.
    have hNearT x (hx : B0 x) : inner_norm (@euclidean_inner_productP R n) (T (f x-f a))<=d.
      exact: ltW (hS x hx.2).2.
    have hImageNear z (hz : (F @` B0) z) :
        inner_norm (@euclidean_inner_productP R n) (L (val z-f a))<=r.
      have [x hx <-] := hz; exact: hNearL x hx.
    have hHaus := hHausdorff m%:R hp (F @` B0) hImageNear.
    have hImage : (fun z : M=>L (val z)) @` (F @` B0)=(fun x : X=>L (f x)) @` B0.
      apply/seteqP; split=> y.
      + move=> [z [x hx <-] <-]; by exists x.
      + move=> [x hx <-]; exists (F x); first by exists x.
        by [].
    rewrite hImage real_hausdorff_measure_natural
      real_power_natural_exponent in hHaus; last exact: ltW hLambda0.
    have [K [hK hKBound]] := @euclidean_positive_linear_metric_bound R n L.
    have [B [hB hBound]] := hLip.
    have hFrozenLip : @is_metric_lipschitz R X E setT (fun x=>L (f x)).
      exists (K*B); split; first exact: mulr_gt0 hK hB; split.
      + exact: ltW (mulr_gt0 hK hB).
      + move=> x y _ _.
        apply: le_trans (hKBound.2 (f x) (f y) Logic.I Logic.I) _.
        rewrite -mulrA; exact (ler_wpM2l (ltW hK) (hBound.2 x y Logic.I Logic.I)).
    have hFrozenInj : {in E0 &, injective (fun x : X=>L (f x))}.
      move=> x y hx hy hEq; exact (hInj _ _ hx hy ((positive_norm_factor_injective hL) _ _ hEq)).
    have hArea := @euclidean_piece_area_density R m n (fun x=>L (f x)) E0 hFrozenLip hE0 hFrozenInj.
    have hFrozen := congr1 (fun measure=>measure S) hArea.
    change (@hausdorff_measure R E m ((fun x : X=>L (f x)) @` B0)=
      euclidean_jacobian_measure (fun x=>L (f x)) B0) in hFrozen.
    rewrite hFrozen in hHaus.
    have hVectors x (hx : B0 x) v :
        inner_norm (riemannian_tensor_inner hh (hf a)) v<=
          lambda*inner_norm (riemannian_tensor_inner hh (hf x)) v /\
        inner_norm (riemannian_tensor_inner hh (hf x)) v<=
          lambda*inner_norm (riemannian_tensor_inner hh (hf a)) v.
      have hVectorBounds := (hTensor (f x) (hNearT x hx)).2 v.
      rewrite (riemannian_tensor_speed_inner_norm hh (hf x))
        (positive_norm_factor_norm hT) in hVectorBounds.
      split; last exact hVectorBounds.2.
      have hScaled := ler_wpM2l (ltW hLambda0) hVectorBounds.1.
      by rewrite mulrA mulfV // mul1r in hScaled.
    have hJ := @frozen_riemannian_area_density_bounds R m n A h hh f hf
      (f a) (hf a) L lambda B0 hLip hLambda0 hL hVectors.
    have hCoefficient : (0<=(lambda^+m)%:E)%E by rewrite lee_fin; exact: exprn_ge0 (ltW hLambda0).
    split.
    + have hCombined := le_trans hHaus.2 (lee_wpmul2l hCoefficient hJ.1).
      by rewrite muleA -EFinM -exprD in hCombined.
    + have hCombined := le_trans hJ.2 (lee_wpmul2l hCoefficient hHaus.1).
      by rewrite muleA -EFinM -exprD in hCombined.
have hEqual := @measure_local_geometric_squeeze R X mu nu U (m+m)%N
  hMu hNu hBase hBorel hLocal.
exact hEqual.
Qed.
