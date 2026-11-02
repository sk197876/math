(** Federer (1969), 3.2.35, p. 272:
    the explicit normalized projection averages
    in Steiner's dimension induction. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  EuclideanProjectionSpace EuclideanProjectionMetric EuclideanProjectionComposition EuclideanProjectionConvexImage
  EuclideanProjectionBoundedImage ConvexProjectedIntrinsicVolumeAverage ConvexIntrinsicVolumeIntegrals
  IntegralGeometricGauge ProjectionBeta OrthogonalProjectionProbability PartialFunctionBasic ExtendedRealOrderTopology
  MeasureIntegralUP TotalNonnegativeExtendedScaleIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_projected_intrinsic_volume_ratio]:
    supporting each averaged coefficient in the
    last display of Federer 3.2.35, p. 272.
    The proved two-order projection integral and
    positivity of the existing beta_1(k,m) give
    the actual integral of zeta^m(p(S)) as
    beta_1(n,m)/beta_1(k,m) times zeta^m(S).
    Every auxiliary projection law is discharged
    from the given actual composition, with no
    source measurability or positive-degree premise. *)
Theorem convex_projected_intrinsic_volume_ratio (R:realType) n k m
    (hkn:(k<=n)%N) (hmk:(m<=k)%N)
    (C:orthogonal_projection_metric_space R k m*orthogonal_projection_metric_space R n k->
      orthogonal_projection_metric_space R n m)
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_euclidean_projection_composition C ->S!=set0 ->is_inner_convex S ->metric_set_bounded S ->
  is_measure_integral (@orthogonal_projection_probability R n k hkn)
    (partial_function_total (fun p=>(@integral_geometric_gauge R k m hmk 1
      (euclidean_projection_linear p @` S):extended_real_line R)))
    ((@projection_beta R n m (leq_trans hmk hkn) 1 / @projection_beta R k m hmk 1)%R%:E*
      @integral_geometric_gauge R n m (leq_trans hmk hkn) 1 S).
Proof.
move=>hC hNonempty hS hBound.
pose P:=orthogonal_projection_metric_space R n k.
pose theta:=@orthogonal_projection_probability R n k hkn.
pose b:=@projection_beta R k m hmk 1.
pose B:=@projection_beta R n m (leq_trans hmk hkn) 1.
pose g (p:P):extended_real_line R:=@integral_geometric_gauge R k m hmk 1 (euclidean_projection_linear p @` S).
pose G:=@integral_geometric_gauge R n m (leq_trans hmk hkn) 1 S.
have hb:(0<b)%R:=@projection_beta_positive R k m hmk 1 (lexx 1).
have hb0:(b!=0)%R by rewrite gt_eqF.
have hGNonnegative p:0<=g p.
  have hTNonempty:euclidean_projection_linear p @` S!=set0.
    have [a ha]:=hNonempty; exists (euclidean_projection_linear p a); by exists a.
  exact:(@convex_intrinsic_volume_nonnegative_finite R k m hmk 1 _ hTNonempty
    (@euclidean_projection_convex_image R n k p S hS)
    (@euclidean_projection_bounded_image R n k p S hBound) (lexx 1)).1.
have hNormalized:is_measure_integral theta
    (partial_function_total (fun p:P=>(b%:E*g p:extended_real_line R))) (B%:E*G).
  exact:(@convex_projected_intrinsic_volume_average R n k m hkn hmk C S hC hNonempty hS hBound).
have hPositive p:0<=b%:E*g p:=mule_ge0 (lee_tofin (ltW hb)) (hGNonnegative p).
have hInverse:0<=b^-1%R%:E by rewrite lee_fin invr_ge0; exact:ltW hb.
have hScaled:=@total_nonnegative_extended_scale_integral R P theta
  (@theta_star_is_measure R n k hkn) (fun p:P=>(b%:E*g p:extended_real_line R))
  (B%:E*G) b^-1%R%:E hPositive hNormalized hInverse.
have hFunctions:(fun p:P=>(b^-1%R%:E*(b%:E*g p):extended_real_line R))=g.
  apply:funext=>p; by rewrite muleA -EFinM mulVf // mul1e.
have hValue:b^-1%R%:E*(B%:E*G)=(B/b)%R%:E*G.
  by rewrite muleA -EFinM mulrC.
by rewrite hFunctions hValue in hScaled.
Qed.
