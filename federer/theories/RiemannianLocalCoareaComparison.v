(** Federer (1969), 3.2.46, p. 282: actual
    Riemannian coarea is locally as close as desired
    to frozen Euclidean coarea. Every coordinate patch,
    factor, density bound, Jacobian comparison and genuine
    integral below is proved from the original hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanLinearMaps PositiveSymmetricNormFactor PositiveNormFactorDiscriminant
  RiemannianTensorUP RiemannianMetricCarrier RiemannianHausdorff RiemannianPathLipschitz
  RiemannianChartReference RiemannianChartVolumeDensity RiemannianChartEllipsoid
  RiemannianVolumeCompletion RiemannianJacobianDensityMeasure
  RiemannianLocalTwoMetricJacobian RiemannianLocalFibreMassComparison
  RiemannianLocalVolumeDensityBounds RiemannianFrozenCoarea
  RiemannianFrozenCoareaSourceComparison RiemannianCoareaTargetDensityComparison
  RiemannianCoareaFibreMeasurable NonnegativeIntegralSandwich CoareaLocalDistortionAlgebra
  MappingMultiplicity HausdorffMeasure PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureIntegralUP MeasurableFunctionUP TopologicalBorel
  LipschitzUP NormMetricScaleContinuity ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_local_coarea_comparison]:
    the proved local coarea comparison underlying the
    extension of 3.2.11, p. 249, in
    3.2.46, p. 282. Only n<m and
    original path-Lipschitz continuity are required to
    produce the local patch. Every completed measurable
    original subset on that patch has a genuine
    whole-fibre integral, with arbitrarily small fixed
    power distortion and no rank or finite-mass premise. *)
Theorem riemannian_local_coarea_comparison (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hpSource : 0<=m%:R :> R) (hpTarget : 0<=n%:R :> R)
    (hpFibre : 0<=(m-n)%:R :> R) :
  (n<m)%N -> is_riemannian_path_lipschitz f ->
  forall lambda : R, 1<lambda -> forall a : riemannian_metric_space hg,
  exists V : set (riemannian_metric_space hg), open V /\ V a /\
    forall S, measure_measurable (riemannian_hausdorff_measure hg m%:R hpSource) S ->
    S `<=` V -> exists b, (0<=b)%E /\
      is_measure_integral (riemannian_hausdorff_measure hh n%:R hpTarget)
        (partial_function_total (fun y=>(riemannian_hausdorff_measure hg (m-n)%:R hpFibre
          (mapping_fibre f S y) : extended_real_line R))) b /\
      (riemannian_jacobian_measure f hpSource n S<=
        (lambda^+((n+n).+1+(m-n)+1))%:E*b)%E /\
      (b<=(lambda^+((n+n).+1+(m-n)+1))%:E*
        riemannian_jacobian_measure f hpSource n S)%E.
Proof.
move=> hnm hLip lambda hLambda a.
pose X := [the metricType R of riemannian_metric_space hg].
pose Y := [the metricType R of riemannian_metric_space hh].
pose E := [the metricType R of inner_metric_space (@euclidean_inner_productP R m)].
pose sigma := riemannian_hausdorff_measure hg (m-n)%:R hpFibre.
pose beta := riemannian_hausdorff_measure hh n%:R hpTarget.
have hLambda0 : 0<lambda := lt_trans ltr01 hLambda.
have hBeta := @riemannian_hausdorff_is_measure R n B h hh n%:R hpTarget.
have hCont : continuous f.
  have [K [hK hBound]] := @riemannian_path_lipschitz_carrier R m n A B g h hg hh f hLip.
  apply:(@metric_fixed_lipschitz_continuous R X Y f K (ltW hK)).
  by move=> x y; exact:hBound.2 x y Logic.I Logic.I.
have [L [r [hr [hL hFibre]]]] :=
  @riemannian_local_fibre_mass_comparison R m A g hg (val a) (set_valP a) lambda hLambda.
have [M hM] := positive_symmetric_norm_factor_exists (riemannian_tensor_inner hh (set_valP (f a))).
have [I [hLI hIL]] := euclidean_linear_inverse (positive_norm_factor_injective hL).
have [L0 [M0 [d [e [hd [he [hL0 [hM0 [hPatchSource [hPatchTarget hJac]]]]]]]]]] :=
  @riemannian_local_two_metric_jacobian_bounds R m n A B g h hg hh
    (val a) (set_valP a) (val (f a)) (set_valP (f a)) lambda hLambda.
have [U [K [F [hU [hUa [hUA [hK [hFLipBound [hRange hAgree]]]]]]]]] :=
  @riemannian_path_map_local_coordinates R m n A B g h hg hh f hLip a.
have hFLip : is_metric_lipschitz setT F by exists K; split.
have [Vs [hVs [hVsa hSourceDensity]]] :=
  @riemannian_local_volume_density_bounds R m A g hg a lambda hLambda.
have [Wt [hWt [hWta hTargetDensity]]] :=
  @riemannian_local_volume_density_bounds R n B h hh (f a) lambda hLambda.
pose V0 : set X := (fun x : X=>(val x : E)) @^-1` U.
pose V1 := [set x : X | inner_norm (@euclidean_inner_productP R m) (L (val x-val a))<r].
pose V2 := [set x : X | inner_norm (@euclidean_inner_productP R m) (L0 (val x-val a))<d].
pose V3 := f @^-1` [set y : Y |
  inner_norm (@euclidean_inner_productP R n) (M0 (val y-val (f a)))<e].
pose Vt := f @^-1` Wt.
pose V := V0 `&` (V1 `&` (V2 `&` (V3 `&` (Vs `&` Vt)))).
have hV0 : open V0 := @open_comp X E (fun x=>val x) U
  (fun x _=>@riemannian_chart_inclusion_continuous R m A g hg x) hU.
have hV1 : open V1 := @riemannian_chart_ellipsoid_open R m A g hg L (val a) r.
have hV2 : open V2 := @riemannian_chart_ellipsoid_open R m A g hg L0 (val a) d.
have hV3 : open V3 := @open_comp X Y f _ (fun x _=>hCont x)
  (@riemannian_chart_ellipsoid_open R n B h hh M0 (val (f a)) e).
have hVt : open Vt := @open_comp X Y f Wt (fun x _=>hCont x) hWt.
have hVa : V a.
  split; first exact hUa.
  split.
  - change (is_true (inner_norm (@euclidean_inner_productP R m) (L (val a-val a))<r)).
    by rewrite subrr linear0 inner_norm0.
  split.
  - change (is_true (inner_norm (@euclidean_inner_productP R m) (L0 (val a-val a))<d)).
    by rewrite subrr linear0 inner_norm0.
  split.
  - change (is_true (inner_norm (@euclidean_inner_productP R n) (M0 (val (f a)-val (f a)))<e)).
    by rewrite subrr linear0 inner_norm0.
  by split.
exists V; split.
- exact:openI hV0 (openI hV1 (openI hV2 (openI hV3 (openI hVs hVt)))).
split; first exact hVa.
move=> S hS hSV.
have hReferenceS := (@riemannian_volume_reference_measurable_iff R m A g hg hpSource S).1 hS.
have hSAgreement x (hx : S x) := hAgree x (hSV x hx).1.
have [t [hFrozenSource hFrozenTarget]] :=
  @riemannian_frozen_coarea_reference_integrals R m n A B g h hg hh f F S L I M
    hnm hLI hIL (positive_norm_factor_injective hM) hFLip hReferenceS hSAgreement.
have hDetL : 0<euclidean_det L := positive_norm_factor_det_positive hL.
have hDetM : 0<euclidean_det M := positive_norm_factor_det_positive hM.
rewrite (ger0_norm (ltW hDetL)) (ger0_norm (ltW hDetM)) in hFrozenTarget.
have hSource := @riemannian_frozen_coarea_source_bounds R m n A B g h hg hh f hpSource
  (val a) (set_valP a) (val (f a)) (set_valP (f a)) L I M U F S (lambda^+(n+n)) lambda t
  hLip hFLip hU hUA hAgree (fun x hx=>(hSV x hx).1) hS hL hM hLI
  (exprn_gt0 (n+n) hLambda0) hLambda0.
have hSourceBound := hSource
  (fun x hx D=>hJac (val x) (set_valP x) (val (f x)) (set_valP (f x))
    (ltW (hSV x hx).2.2.1) (ltW (hSV x hx).2.2.2.1) n D)
  (fun x hx=>hSourceDensity L hL x (hSV x hx).2.2.2.2.1) hFrozenSource.
rewrite -exprSr in hSourceBound.
have [q [hTargetIntegral [hTargetUpper hTargetLower]]] :=
  @riemannian_coarea_target_density_bounds R m n A B g h hg hh f L S hpTarget lambda
    (euclidean_det M) _ hLambda0 hDetM
    (fun x hx=>hTargetDensity M hM (f x) (hSV x hx).2.2.2.2.2) hFrozenTarget.
have hCommon : ((euclidean_det M)%:E*((euclidean_det M)^-1%:E*
    ((euclidean_det L)%:E*t)))%E=((euclidean_det L)%:E*t)%E.
  by rewrite muleA -EFinM mulfV ?gt_eqF // mul1e.
rewrite hCommon in hTargetUpper hTargetLower.
pose p := fun y : Y=>(sigma (mapping_fibre f S y) : extended_real_line R).
pose qf := fun y : Y=>(@hausdorff_measure R E (m-n)
  ((fun x : X=>L (val x)) @` mapping_fibre f S y) : extended_real_line R).
have hMass := @riemannian_coarea_fibre_mass_measurable R m n A B g h hg hh f
  hpSource hpTarget hpFibre S (ltnW hnm) hLip hS.
have hFibreBounds y : (p y<=(lambda^+(m-n))%:E*qf y)%E /\
    (qf y<=(lambda^+(m-n))%:E* p y)%E.
  have hBounds := @hFibre Y f S (m-n)%N hpFibre
    (fun x hx=>ltW (hSV x hx).2.1) y.
  exact:conj hBounds.2 hBounds.1.
have [b [hb0 [hActual [hActualUpper hActualLower]]]] :=
  @nonnegative_integral_two_sided_bounds R Y beta p qf (lambda^+(m-n)) q hBeta
    (exprn_gt0 (m-n) hLambda0) (fun y=>measure_nonnegative
      (@riemannian_hausdorff_is_measure R m A g hg (m-n)%:R hpFibre) _) hMass hTargetIntegral hFibreBounds.
exists b; split; first exact hb0; split; first exact hActual.
exact (@coarea_local_distortion_algebra R lambda (n+n).+1 (m-n)
  (riemannian_jacobian_measure f hpSource n S) ((euclidean_det L)%:E*t)%E q b hLambda0
  hSourceBound.1 hSourceBound.2 hTargetUpper hTargetLower hActualUpper hActualLower).
Qed.
