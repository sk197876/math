(** Federer (1969), 3.2.38, p. 275: the actual good-cube
    affine tube bound, using every term of the Steiner polynomial. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology ring.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric InnerNorm InnerConvex
  HilbertFormCompactness HomSpaceTopology EuclideanLinearJacobian LinearJacobianSandwich
  EuclideanLebesgueDimensions EuclideanBallVolume MetricOpenThickening MinkowskiContentsBasic
  EuclideanCoordinateCubeUP EuclideanCoordinateCubeGeometry EuclideanAffineImageGeometry
  CompactSetDistanceProfile CompactMetricBounded IntegralGeometricGauge ProjectionBeta
  SteinerTubePolynomial SteinerTubeScalarPolynomial ConvexIntrinsicFinitePart
  CompactConvexOpenTubePolynomial AffineConvexIntrinsicTop AffineCubeIntrinsicCap
  HausdorffNullIntrinsicGauge GridSteinerPolynomialBound LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [affine_coordinate_cube_steiner_estimate]: the full
    affine good-cube estimate behind rho(K)<=integral_K J_m f+
    xi/v L^m(K), Federer 3.2.38, p. 275. The constant xi depends
    only on m,n,L. All actual normalized coefficients are proved:
    the top is J_m D times cube volume, higher ones vanish, and
    lower ones have uniform actual projected-ball caps. The printed
    sum's missing j=0 term is retained and included in xi. This
    keeps singular maps, L=0 and all admissible natural dimensions;
    no coefficient, affine-image or Jacobian premise is assumed. *)
Theorem affine_coordinate_cube_steiner_estimate (R:realType) m n (hmn:(m<=n)%N) (L:R):
  0<=L ->exists xi:R,0<=xi /\forall v:nat,forall (r:R) (corner a:R_n R m) (b:R_n R n)
    (Q:set (inner_metric_space (@euclidean_inner_productP R m)))
    (D:Hom (R_n R m) (R_n R n)),
    (0<v)%N ->0<r ->is_euclidean_coordinate_cube corner (v%:R*r) Q ->Q a ->
    (forall u,inner_norm (@euclidean_inner_productP R n) (D u)<=
      L*inner_norm (@euclidean_inner_productP R m) u) ->
    (@euclidean_lebesgue_measure R n
      (@metric_open_thickening R (inner_metric_space (@euclidean_inner_productP R n)) ((fun x=>(b+D (x-a))%R) @` Q) (((1+m%:R/v%:R)*r)%R))*
      ((euclidean_unit_ball_volume R (n-m)*r^+(n-m))%R%:E)^-1<=
      ((euclidean_linear_jacobian m D+xi/v%:R)*(v%:R*r)^+m)%R%:E)%E.
Proof.
move=>hL.
pose alpha:=euclidean_unit_ball_volume R (n-m).
have hAlpha:0<alpha:=(euclidean_unit_ball_volumeE R (n-m)).2.
pose c (i:'I_n.+1):R:=(@projection_beta R n i (steiner_dimension_guard i) 1)^-1*
  euclidean_unit_ball_volume R i*(L* m%:R)^+i*euclidean_unit_ball_volume R (n-i)/alpha.
have hc i:0<=c i.
  have hBeta:0<=(@projection_beta R n i (steiner_dimension_guard i) 1)^-1.
    rewrite invr_ge0; exact:ltW (@projection_beta_positive R n i (steiner_dimension_guard i) 1 (lexx 1%E)).
  have hPower:0<=(L* m%:R)^+i:=exprn_ge0 _ (mulr_ge0 hL (ler0n R m)).
  exact:divr_ge0 (mulr_ge0 (mulr_ge0 (mulr_ge0 hBeta
    (ltW (euclidean_unit_ball_volumeE R i).2)) hPower)
    (ltW (euclidean_unit_ball_volumeE R (n-i)).2)) (ltW hAlpha).
pose U:R:=(1+m%:R)^+n.
pose P:R:=\sum_(i<n-m) (1+m%:R)^+i.
pose xi:R:=U*(\sum_i c i)+L^+m* m%:R*P.
have hXi:0<=xi.
  apply:addr_ge0.
  - apply:mulr_ge0; first exact:exprn_ge0 _ (addr_ge0 ler01 (ler0n R m)).
    apply:sumr_ge0=>i _; exact:hc.
  - apply:mulr_ge0.
    + exact:mulr_ge0 (exprn_ge0 _ hL) (ler0n R m).
    + apply:sumr_ge0=>i _; exact:exprn_ge0 _ (addr_ge0 ler01 (ler0n R m)).
exists xi; split=>// v r corner a b Q D hv hr hQ ha hDN.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose V:R:=v%:R.
pose A:R:=1+m%:R/V.
pose g:X->Y:=fun x=>b+D (x-a).
pose S:set Y:=g @` Q.
pose offset:Y:=b-D a.
have hFunction:g=(fun x:X=>offset+D x).
  apply:funext=>x; by rewrite /g /offset linearB addrAC addrA.
have hQN:Q!=set0 by exists a.
have hQC:compact Q:=coordinate_cube_compact hQ.
have hQV:is_inner_convex Q:=coordinate_cube_convex hQ.
have hSC:compact S.
  rewrite /S hFunction; exact:(@euclidean_affine_hom_compact_image R m n D offset Q hQC).
have hSV:is_inner_convex S.
  rewrite /S hFunction; exact:(@affine_hom_convex_image R (R_n R m) (R_n R n) D offset Q hQV).
have hSN:S!=set0 by exists (g a); exists a.
pose C:compact_metric_set Y:=exist _ S (mem_set (conj hSC hSN)).
have hSB:=compact_metric_diameter_finite C.
have hGLip:is_metric_lipschitz_bound setT g
    (hom_operator_norm (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
      (@coordinate_basisP R m) D).
  rewrite hFunction; exact:euclidean_affine_hom_lipschitz_bound.
pose coeff (i:'I_n.+1):R:=fine (@integral_geometric_gauge R n i (steiner_dimension_guard i) 1 S).
pose normalized (i:'I_n.+1):R:=coeff i*euclidean_unit_ball_volume R (n-i)/alpha.
have hCoeffE (i:'I_n.+1):@integral_geometric_gauge R n i (steiner_dimension_guard i) 1 S=(coeff i)%:E.
  exact:(@convex_intrinsic_finite_part_value R n i (steiner_dimension_guard i) S hSN hSV hSB).
have hHigh (i:'I_n.+1):(m<i)%N ->normalized i=0.
  move=>hmi; have hNull:=@above_source_dimension_image_intrinsic_zero R m n i
    (steiner_dimension_guard i) g _ Q hmi hGLip.
  by rewrite /normalized /coeff /S hNull /= mul0r mul0r.
pose iM:'I_n.+1:=Ordinal (leq_ltn_trans hmn (ltnSn n)).
have hTop:normalized iM=euclidean_linear_jacobian m D*(V*r)^+m.
  have hActual:=@affine_convex_top_intrinsic_volume R m n (steiner_dimension_guard iM)
    D a b Q hQN hQC hQV.
  rewrite (coordinate_cube_volume hQ) -EFinM in hActual.
  have hCoeff:coeff iM=euclidean_linear_jacobian m D*(V*r)^+m.
    exact:(congr1 fine hActual).
  rewrite /normalized hCoeff /iM /= /alpha mulfK //.
  exact:lt0r_neq0 hAlpha.
have hLow (i:'I_n.+1):(i<m)%N ->normalized i<=c i*(V*r)^+i.
  move=>him.
  have hCap:=@affine_coordinate_cube_intrinsic_cap R m n i (steiner_dimension_guard i)
    corner a b (V*r) L Q D hQ ha hL hDN.
  rewrite (hCoeffE i) lee_fin in hCap.
  pose W:R:=euclidean_unit_ball_volume R (n-i)/alpha.
  have hW:0<=W:=divr_ge0 (ltW (euclidean_unit_ball_volumeE R (n-i)).2) (ltW hAlpha).
  have hScaled:=ler_wpM2r hW hCap.
  have hLeft:coeff i*W=normalized i by rewrite /W /normalized; ring.
  have hRight:((@projection_beta R n i (steiner_dimension_guard i) 1)^-1*
      euclidean_unit_ball_volume R i*(L* m%:R)^+i*(V*r)^+i)*W=c i*(V*r)^+i.
    by rewrite /W /c; ring.
  by rewrite hLeft hRight in hScaled.
have hV:0<V by rewrite /V ltr0n.
have hVOne:1<=V by rewrite /V ler1n.
have hJ0:0<=euclidean_linear_jacobian m D:=euclidean_linear_jacobian_nonnegative m D.
have hLower u:0*inner_norm (@euclidean_inner_productP R m) u<=
    inner_norm (@euclidean_inner_productP R n) (D u).
  rewrite mul0r; exact:inner_norm_nonnegative.
have hJUpper:euclidean_linear_jacobian m D<=L^+m.
  exact:(euclidean_top_jacobian_sandwich (lexx 0) hL hLower hDN).2.
have hPolynomial:=@grid_steiner_polynomial_bound R m n hmn V r
  (euclidean_linear_jacobian m D) (L^+m) normalized c hVOne hr hJ0 hJUpper hc hHigh hTop hLow.
have hA:0<A.
  apply:lt_le_trans ltr01 _; rewrite /A lerDl; apply:divr_ge0; [exact:ler0n|exact:ltW hV].
have hRadius:0<A*r:=mulr_gt0 hA hr.
have hVolume:@euclidean_lebesgue_measure R n (metric_open_thickening S (A*r))=
    (\sum_(i:'I_n.+1) coeff i*(euclidean_unit_ball_volume R (n-i)*(A*r)^+(n-i)))%:E.
  rewrite (compact_convex_open_tube_polynomial hSC hSN hSV hRadius).
  exact:(@steiner_tube_polynomial_scalar_value R n S (A*r) hSN hSV hSB).
have hNumerator:(\sum_(i:'I_n.+1) normalized i*(A*r)^+(n-i))=
    (\sum_(i:'I_n.+1) coeff i*(euclidean_unit_ball_volume R (n-i)*(A*r)^+(n-i)))/alpha.
  rewrite mulr_suml; apply:eq_bigr=>i _; rewrite /normalized; ring.
have hRatio:(\sum_(i:'I_n.+1) coeff i*(euclidean_unit_ball_volume R (n-i)*(A*r)^+(n-i)))/
      (alpha*r^+(n-m))=
    (\sum_(i:'I_n.+1) normalized i*(A*r)^+(n-i))/r^+(n-m).
  rewrite hNumerator invfM; ring.
have hDenominator:0<alpha*r^+(n-m):=mulr_gt0 hAlpha (exprn_gt0 _ hr).
change (is_true (@euclidean_lebesgue_measure R n (metric_open_thickening S (A*r))*
    ((alpha*r^+(n-m))%:E)^-1<=
    ((euclidean_linear_jacobian m D+xi/V)*(V*r)^+m)%:E)%E).
rewrite hVolume inver (gt_eqF hDenominator) -EFinM lee_fin hRatio.
have hAlgebra:euclidean_linear_jacobian m D*(V*r)^+m+
    (((1+m%:R)^+n*(\sum_i c i)+L^+m* m%:R*(\sum_(i<n-m) (1+m%:R)^+i))/V)*(V*r)^+m=
    (euclidean_linear_jacobian m D+xi/V)*(V*r)^+m by rewrite /xi /U /P; ring.
by rewrite hAlgebra in hPolynomial.
Qed.
