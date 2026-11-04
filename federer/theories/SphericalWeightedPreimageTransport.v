(** Federer (1969), 3.2.48, pp. 284, 286: signed
    weight transport by Phi. The exact image measure follows
    from 3.2.47(3); finite completed-source regularity proves
    composition measurability before the signed integral is used. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanHomInnerCharts UnitSphereSpace SphericalProductPreimageImage
  SphericalFinitePullback SphericalPullbackPushforward RectifiableSetUP
  HausdorffMeasure HausdorffClosedCoverAgreement MeasureUP MeasureRestriction
  MeasurePushforward MeasureScaleIntegral MeasureIntegralUP
  PartialFunctionUP PartialFunctionPrecomposition ExtendedRealOrderTopology
  BorelRegularMeasureUP BorelRegularFiniteRestriction
  PushforwardMeasurableFunctions PushforwardIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_weighted_pullback_from_preimage]: the
    actual weighted form of 3.2.47(3) used on a fibre
    in 3.2.48, p. 284. Completed measurability of the
    actual preimage suffices; E itself is not assumed measurable.
    Partial signed weights and their exact domains remain.
    The coefficient and every measurability premise are derived;
    a separate composition-measurability hypothesis is not imposed. *)
Theorem spherical_weighted_pullback_from_preimage (R:realType) n r
    (c:R_n R n.+1) (E:set (R_n R n.+1))
    (u:partial_function (R_n R n.+1) (extended_real_line R)) a:
  inner_norm (@euclidean_inner_productP R n.+1) c= 1 ->
  E `<=` @euclidean_unit_sphere_set R n.+1 ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n.+1)) r) r E ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1)) (r+n*(n-1)%/2)%N)
    (spherical_orthogonal_preimage c E) ->
  is_measure_integral (measure_restrict (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n.+1)) r) E) u a ->
  is_measure_integral (measure_restrict (@hausdorff_measure R
    (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1)) (r+n*(n-1)%/2)%N)
    (spherical_orthogonal_preimage c E))
    (partial_function_precompose (fun g:Hom (R_n R n.+1) (R_n R n.+1)=>g c) u)
    ((spherical_preimage_mass_scale R n r)%:E*a)%E.
Proof.
move=>hc hES hRect hPreMeas hI.
pose X:=inner_metric_space (@euclidean_inner_productP R n.+1).
pose Y:=inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1).
pose beta:=measure_restrict (@hausdorff_measure R X r) E.
pose rho:=measure_restrict (@hausdorff_measure R Y (r+n*(n-1)%/2)%N)
  (spherical_orthogonal_preimage c E).
pose F:=fun g:Hom (R_n R n.+1) (R_n R n.+1)=>g c.
have hBeta:=measure_restrict_is_measure (@hausdorff_measure_is_measure R X r) E.
have hRho:=measure_restrict_is_measure (@hausdorff_measure_is_measure R Y (r+n*(n-1)%/2)%N)
  (spherical_orthogonal_preimage c E).
have hPreRect:=@spherical_finite_rectifiable_pullback R n r c E hc hES hRect.
have hReg:is_borel_regular_measure rho.
  exact (@borel_regular_finite_measurable_restriction R Y
    (@hausdorff_measure R Y (r+n*(n-1)%/2)%N)
    (@hausdorff_measure_is_measure R Y (r+n*(n-1)%/2)%N)
    (@hausdorff_measure_borel_regular R Y (r+n*(n-1)%/2)%N)
    (spherical_orthogonal_preimage c E) hPreMeas hPreRect.2).
have hFinite:(rho setT< +oo)%E.
  rewrite /rho /measure_restrict setIT; exact hPreRect.2.
have hPush:=@spherical_pullback_pushforward R n r c E hc hES hRect.
have hScale:=@measure_scale_integral R X beta hBeta (spherical_preimage_mass_scale R n r)
  (spherical_preimage_mass_scale_positive R n r) u a hI.
rewrite -hPush in hScale.
have hComposition:=@regular_pushforward_measurable_composition R Y X
  (extended_real_line R) rho hRho (borel_regular_is_regular hRho hReg) F u hFinite hScale.1.
exact ((@measure_pushforward_integral_iff R Y X rho hRho F u hComposition _).2 hScale).
Qed.


(** Source for [spherical_weighted_pullback_from_preimage_iff]:
    the weighted preimage equality used on actual fibres
    in 3.2.48, p. 284, including definedness in both
    directions. Positive finite preimage mass scaling is cancelled;
    no original E measurability or additional fibre integrability
    premise is introduced. *)
Theorem spherical_weighted_pullback_from_preimage_iff (R:realType) n r
    (c:R_n R n.+1) (E:set (R_n R n.+1))
    (u:partial_function (R_n R n.+1) (extended_real_line R)) a:
  inner_norm (@euclidean_inner_productP R n.+1) c= 1 ->
  E `<=` @euclidean_unit_sphere_set R n.+1 ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n.+1)) r) r E ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1)) (r+n*(n-1)%/2)%N)
    (spherical_orthogonal_preimage c E) ->
  is_measure_integral (measure_restrict (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n.+1)) r) E) u a <->
  is_measure_integral (measure_restrict (@hausdorff_measure R
    (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1)) (r+n*(n-1)%/2)%N)
    (spherical_orthogonal_preimage c E))
    (partial_function_precompose (fun g:Hom (R_n R n.+1) (R_n R n.+1)=>g c) u)
    ((spherical_preimage_mass_scale R n r)%:E*a)%E.
Proof.
move=>hc hES hRect hPreMeas; split.
- exact (@spherical_weighted_pullback_from_preimage R n r c E u a hc hES hRect hPreMeas).
- move=>hI.
  pose X:=inner_metric_space (@euclidean_inner_productP R n.+1).
  pose Y:=inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1).
  pose beta:=measure_restrict (@hausdorff_measure R X r) E.
  pose rho:=measure_restrict (@hausdorff_measure R Y (r+n*(n-1)%/2)%N)
    (spherical_orthogonal_preimage c E).
  pose F:=fun g:Hom (R_n R n.+1) (R_n R n.+1)=>g c.
  pose C:=spherical_preimage_mass_scale R n r.
  have hC:0<C:=spherical_preimage_mass_scale_positive R n r.
  have hCInverse:0<C^-1 by rewrite invr_gt0.
  have hBeta:=measure_restrict_is_measure (@hausdorff_measure_is_measure R X r) E.
  have hRho:=measure_restrict_is_measure (@hausdorff_measure_is_measure R Y (r+n*(n-1)%/2)%N)
    (spherical_orthogonal_preimage c E).
  have hPush:=@spherical_pullback_pushforward R n r c E hc hES hRect.
  have hPushed:=(@measure_pushforward_integral_iff R Y X rho hRho F u hI.1 _).1 hI.
  rewrite hPush in hPushed.
  have hRestore:=@measure_scale_integral R X (measure_scale C beta)
    (measure_scale_is_measure hBeta hC) C^-1 hCInverse u (C%:E*a)%E hPushed.
  rewrite (measure_scale_inverse beta hC) in hRestore.
  have hValue:(C^-1%:E*(C%:E*a)=a)%E.
    by rewrite muleA -EFinM mulVf ?gt_eqF // mul1e.
  by rewrite hValue in hRestore.
Qed.
