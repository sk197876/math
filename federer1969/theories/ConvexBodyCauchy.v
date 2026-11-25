(** Federer (1969), 3.2.35, pp. 271--272:
    Cauchy's boundary formula for every original
    nonempty bounded open convex body. The
    corrected radial boundary proof applies the
    erratum p. 5, book p. 271 line 24. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  EuclideanOpenConvexBoundary RectifiableFiniteHausdorffMass RectifiableIntegralGeometricMeasure
  ConvexBoundaryProjectionIntegral ProjectionMultiplicityIntegral ProjectedVolumeMeasurability
  SuslinIntegralGeometricMultiplicity IntegralGeometricFirstGaugeIntegral IntegralGeometricGauge
  ProjectionBeta OrthogonalProjectionProbability HausdorffMeasure PartialFunctionBasic
  MeasureIntegralUP MeasureIntegralUniqueness TotalNonnegativeExtendedScaleIntegral
  TopologicalBorel BorelClosedProjection SuslinSetUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_body_cauchy_formula]: the
    complete Cauchy boundary-volume identity in
    Federer 3.2.35, p. 271. The actual
    theta average of boundary counts is beta_1
    times Hausdorff mass by 2.10.15 and
    3.2.26. The proved whole-fibre integral
    is twice each actual projected volume.
    Positivity of the existing beta cancels it.
    No regular boundary, normal field, Jacobian,
    finite-to-one or projection identity is assumed.
    The n=1 boundary retains its two H^0 atoms. *)
Theorem convex_body_cauchy_formula (R:realType) k
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+1))):
  S!=set0 ->open S ->is_inner_convex S ->metric_set_bounded S ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R k.+1)) k
    (closure S `\` interior S)=
    (2:R)%:E*@integral_geometric_gauge R k.+1 k (leqnSn k) 1 S.
Proof.
move=>hNonempty hOpen hConvex hBound.
pose X:=inner_metric_space (@euclidean_inner_productP R k.+1).
pose B:=closure S `\` interior S.
pose b:=@projection_beta R k.+1 k (leqnSn k) 1.
have hb:(0<b)%R:=@projection_beta_positive R k.+1 k (leqnSn k) 1 (lexx 1).
have hb0:b!=0%R by rewrite gt_eqF.
have hRect:=@euclidean_open_convex_boundary_rectifiable R k.+1 S hNonempty hOpen hConvex hBound.
rewrite subn1 in hRect.
have hRectMeasure:=rectifiable_hausdorff_measure_rectifiable hRect.
have hBSuslin:@is_suslin_set R X B.
  apply:metric_borel_suslin; apply:closed_borel_set.
  apply:closedI; first exact:closed_closure.
  by rewrite closedC; exact:open_interior.
have hSSuslin:=metric_borel_suslin (open_borel_set hOpen).
have hCrofton:=@suslin_integral_geometric_multiplicity_integral R k.+1 k (leqnSn k) B hBSuslin.
have hAgreement:=(@rectifiable_integral_geometric_hausdorff_agreement R k k.+1
  (leqnSn k) B 1 hRectMeasure (lexx 1)).1.
rewrite hAgreement in hCrofton.
have hVolume:=@integral_geometric_first_gauge_integral R k.+1 k (leqnSn k) S hSSuslin.
have hScaled:=@total_nonnegative_extended_scale_integral R _ _
  (@theta_star_is_measure R k.+1 k (leqnSn k)) (projected_volume_function (m:=k) S)
  _ (2:R)%:E (fun p=>projected_volume_function_nonnegative S p) hVolume (lee_tofin (ler0n R 2)).
have hFunctions:projection_multiplicity_integral (m:=k) B=
    (fun p=>((2:R)%:E*projected_volume_function S p:extended_real_line R)).
  apply/funext=>p; exact:convex_boundary_projection_integral hNonempty hOpen hConvex hBound.
rewrite hFunctions in hCrofton.
pose H:=@hausdorff_measure R X k B.
pose G:=@integral_geometric_gauge R k.+1 k (leqnSn k) 1 S.
have hEquality:b%:E*H=(2:R)%:E*(b%:E*G):=measure_integral_unique hCrofton hScaled.
have hComm:(2:R)%:E*(b%:E*G)=b%:E*((2:R)%:E*G):=muleCA _ _ _.
rewrite hComm in hEquality.
have hCancelScale (z: \bar R):b^-1%R%:E*(b%:E*z)=z.
  by rewrite muleA -EFinM mulVf // mul1e.
have hCancel:=congr1 (fun z: \bar R=>b^-1%R%:E*z) hEquality.
rewrite !hCancelScale in hCancel.
exact hCancel.
Qed.
