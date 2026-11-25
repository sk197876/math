(** Federer (1969), 3.2.36, p. 272:
    the actual intrinsic volumes are continuous
    on nonempty compact convex bodies. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric InnerConvex
  CompactSetDistanceProfile CompactHausdorffMetric CompactMetricBounded CompactConvexVolumeContinuity
  HausdorffEuclideanLocalBound PositiveUniformErrorRadius CompactConvexProjectedVolumeUniformError
  CompactConvexIntrinsicScalarIntegral ProbabilityUniformIntegralError IntegralGeometricGauge
  ConvexIntrinsicVolumeIntegrals ProjectionBeta OrthogonalProjectionProbability EuclideanProjectionMetric
  ProjectedVolumeMeasurability EuclideanBallVolume RealMetricBackground MeasurableRealEmbedding
  ExtendedRealOrderTopology MeasureUP MeasureIntegralUP SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_convex_intrinsic_volume_scalar_continuous]:
    direct intrinsic-volume continuity in Federer
    3.2.36, p. 272. A common source
    norm ball yields a uniform actual projected-
    volume error. The actual finite probability
    integrals and strict positive beta_1(n,m)
    give the normalized intrinsic-volume error.
    This expands the printed deduction without
    an assumed continuity-of-integrals theorem.
    The supporting statement includes m=0;
    every original positive degree is retained. *)
Theorem compact_convex_intrinsic_volume_scalar_continuous (R:realType) n m (hmn:(m<=n)%N):
  continuous (fun A:subspace (@compact_convex_euclidean_class R n)=>
    (fine (@integral_geometric_gauge R n m hmn 1 (val A)):real_line_metric R)).
Proof.
rewrite subspace_continuousP=>A hA U hU.
pose H:=compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n)).
pose P:=orthogonal_projection_metric_space R n m.
pose theta:=@orthogonal_projection_probability R n m hmn.
pose f (B:H):real_line_metric R:=fine (@integral_geometric_gauge R n m hmn 1 (val B)).
have hConvexA:is_inner_convex (val A):=hA.
have [e he hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP (f A) U) hU.
have [c [hc hLocal]]:=hausdorff_euclidean_local_norm_bound A.
pose b:R:=@projection_beta R n m hmn 1.
have hb:0<b:=@projection_beta_positive R n m hmn 1 (lexx 1).
pose C:R:=euclidean_unit_ball_volume R m*(c+1)^+m.
have hC:0<=C.
  apply:mulr_ge0; first exact:ltW (euclidean_unit_ball_volumeE R m).2.
  apply:exprn_ge0; exact:addr_ge0 (ltW hc) ler01.
have heBeta:0<e*b:=mulr_gt0 he hb.
have [d [hd [hd1 hSmall]]]:=positive_uniform_error_radius_exists hC heBeta.
have hNormA x:val A x ->inner_norm (@euclidean_inner_productP R n) x<=c.
  apply:hLocal; by rewrite mdistxx.
have hIntegralA:=@compact_convex_intrinsic_scalar_integral R n m hmn A hConvexA.
have hNeighbourhood:nbhs (A:H) [set B:H|mdist A B<d].
  apply:(metricType_numDomainType.nbhs_mdistP A _).2; by exists d.
change (nbhs (A:H) (fun B:H=>is_inner_convex (val B) ->U (f B))).
apply:(@filterS _ (nbhs A) _ [set B:H|mdist A B<d] _ _ hNeighbourhood)=>B hNear hConvexB.
have hNearOne:mdist A B<1:=lt_le_trans hNear hd1.
have hNormB x:val B x ->inner_norm (@euclidean_inner_productP R n) x<=c.
  exact:hLocal B hNearOne x.
have hUniform (p:P):`|fine (projected_volume_function (val A) p)-fine (projected_volume_function (val B) p)|<=d*C.
  exact:(@compact_convex_projected_volume_uniform_error R n m A B c d hConvexA hConvexB
    (ltW hc) hNormA hNormB hd hd1 hNear p).
have hIntegralB:=@compact_convex_intrinsic_scalar_integral R n m hmn B hConvexB.
have hMean:=@probability_uniform_integral_error R P theta
  (@theta_star_is_measure R n m hmn)
  (fun p:P=>fine (projected_volume_function (val A) p))
  (fun p:P=>fine (projected_volume_function (val B) p))
  (b*f A) (b*f B) (d*C) (@theta_star_total R n m hmn) hIntegralA hIntegralB hUniform.
have hNormalize (u v:R):`|b*u-b*v|<=d*C ->`|u-v|<e.
  move=>hBound; have hStrict:=le_lt_trans hBound hSmall.
  rewrite -mulrBr normrM (ger0_norm (ltW hb)) [e*b]mulrC (ltr_pM2l hb) in hStrict.
  exact:hStrict.
apply:hBall; exact:hNormalize hMean.
Qed.

(** Source for [compact_convex_intrinsic_volume_continuous]:
    the original extended-real intrinsic-volume
    continuity conclusion in Federer 3.2.36,
    p. 272. Finite embedding restores the
    actual gauges on C after their finiteness
    is proved. All m<=n are included,
    with the degree-zero extension explicit;
    no interior or positive-volume premise
    is added to the compact convex source. *)
Theorem compact_convex_intrinsic_volume_continuous (R:realType) n m (hmn:(m<=n)%N):
  continuous (fun A:subspace (@compact_convex_euclidean_class R n)=>
    (@integral_geometric_gauge R n m hmn 1 (val A):extended_real_line R)).
Proof.
have hScalar:=@compact_convex_intrinsic_volume_scalar_continuous R n m hmn.
have hEmbedded:continuous (fun A:subspace (@compact_convex_euclidean_class R n)=>
    ((fine (@integral_geometric_gauge R n m hmn 1 (val A)))%:E:extended_real_line R)).
  move=>A; exact:continuous_comp (hScalar A) (@real_extended_embedding_continuous R _).
apply:(subspace_eq_continuous _ hEmbedded)=>A hA.
have hConvex:is_inner_convex (val A) by move:hA; rewrite inE.
have [hNonnegative hFinite]:=@convex_intrinsic_volume_nonnegative_finite R n m hmn 1 (val A)
  (set_valP A).2 hConvex (compact_metric_diameter_finite A) (lexx 1).
apply:fineK; by rewrite (ge0_fin_numE hNonnegative).
Qed.
