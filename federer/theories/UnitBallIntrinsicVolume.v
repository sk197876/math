(** Federer (1969), 3.2.35, p. 272:
    normalize the coefficients in Steiner's induction
    with the actual unit-ball projection averages. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric InnerNormedTopology
  EuclideanProjectionMetric EuclideanProjectionSpace EuclideanUnitBallProjection EuclideanBallVolume
  EuclideanLebesgueDimensions ProjectedVolumeMeasurability IntegralGeometricGauge ProjectionBeta
  OrthogonalProjectionProbability NonnegativeExtendedProbabilityConstant ExtendedRealOrderTopology
  ConvexBodyCauchy HausdorffUnitSphereMass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [unit_ball_projected_volume]: actual
    projected unit balls have volume alpha(m),
    supporting the last coefficient calculation
    in Federer 3.2.35, p. 272. The
    exact projection image and existing unit-ball
    volume law give the constant function. *)
Lemma unit_ball_projected_volume (R:realType) n m
    (p:orthogonal_projection_metric_space R n m):
  projected_volume_function [set x|inner_norm (@euclidean_inner_productP R n) x<1] p=
    (euclidean_unit_ball_volume R m)%:E.
Proof.
rewrite /projected_volume_function euclidean_unit_ball_projection.
change (euclidean_lebesgue_measure m [set x:inner_metric_space (@euclidean_inner_productP R m)| `|x|<1]=(euclidean_unit_ball_volume R m)%:E).
exact:(euclidean_unit_ball_volumeE R m).1.
Qed.

(** Source for [unit_ball_integral_geometric_gauge]:
    the actual intrinsic volumes of a unit
    ball are alpha(m)/beta_1(n,m), supporting
    the normalization in Federer 3.2.35,
    p. 272. Every projection has the
    proved actual unit-ball volume, so the
    existing probability norm is constant. *)
Theorem unit_ball_integral_geometric_gauge (R:realType) n m (hmn:(m<=n)%N):
  @integral_geometric_gauge R n m hmn 1 [set x|inner_norm (@euclidean_inner_productP R n) x<1]=
    (euclidean_unit_ball_volume R m / @projection_beta R n m hmn 1)%:E.
Proof.
have hFunction:projected_volume_function (m:=m) [set x|inner_norm (@euclidean_inner_productP R n) x<1]=
    (fun _:orthogonal_projection_metric_space R n m=>
      ((euclidean_unit_ball_volume R m)%:E:extended_real_line R)).
  apply:funext=>p; exact:unit_ball_projected_volume.
rewrite /integral_geometric_gauge hFunction
  (@probability_nonnegative_extended_constant_norm R _ _ (@theta_star_is_measure R n m hmn)
    (euclidean_unit_ball_volume R m)%:E 1 (@theta_star_total R n m hmn)
    (lee_tofin (ltW (euclidean_unit_ball_volumeE R m).2)) (lexx _)).
by rewrite -EFinM mulrC.
Qed.

(** Source for [unit_ball_cauchy_coefficient]: the
    alpha/beta coefficient normalization in the
    last line of Federer 3.2.35, p. 272.
    The already proved Cauchy formula on the
    actual unit ball and the sphere-mass formula
    of 3.2.13, p. 250, give the
    same identity as the printed Gamma calculation.
    No Steiner formula or coefficient recurrence
    is assumed. The k= 0 case retains both
    sphere atoms and alpha(0)= 1. *)
Theorem unit_ball_cauchy_coefficient (R:realType) k:
  (k.+1%:R:R)*euclidean_unit_ball_volume R k.+1*
    @projection_beta R k.+1 k (leqnSn k) 1= 2*euclidean_unit_ball_volume R k.
Proof.
pose B:set (inner_metric_space (@euclidean_inner_productP R k.+1)):=
  [set x|inner_norm (@euclidean_inner_productP R k.+1) x<1].
have [hNonempty [hOpen [hConvex hBound]]]:=euclidean_unit_ball_convex_bounded R k.+1.
have hCauchy:=@convex_body_cauchy_formula R k B hNonempty hOpen hConvex hBound.
rewrite /B euclidean_unit_ball_boundary in hCauchy.
have hSphere:=@hausdorff_unit_sphere_mass R k.+1 (ltn0Sn k).
rewrite subn1 /= in hSphere.
rewrite hSphere unit_ball_integral_geometric_gauge -EFinM in hCauchy.
have hEquality:=EFin_inj hCauchy.
pose b:=@projection_beta R k.+1 k (leqnSn k) 1.
have hPositive:0<b:=@projection_beta_positive R k.+1 k (leqnSn k) 1 (lexx _).
have hNonzero:b!=0 by rewrite gt_eqF.
have hScaled:=congr1 (fun x:R=>x*b) hEquality.
change ((k.+1%:R*euclidean_unit_ball_volume R k.+1)*b=
  (2*(euclidean_unit_ball_volume R k/b))*b) in hScaled.
have hCancel:(2*(euclidean_unit_ball_volume R k/b))*b= 2*euclidean_unit_ball_volume R k.
  by rewrite mulrA divfK.
by rewrite hCancel in hScaled.
Qed.
