(** Federer (1969), 3.3.19, p. 306: all
    sufficiently late original small-relative-radius ball
    tests have a local tangent separating their hit children. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric InnerUnitNormalization MetricClosedBalls
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws
  CircularDiscTreeUP CircularDiscLimitUP CircularDiscParentAnnulus CircularDiscRefinement
  CircularUnitVectors CircularUnitVectorSurjection CircularAngleLift CircularUnitCurve
  CircularChildHitAngleWindow CircularChildTangentSeparation CircularTangentPackingWindow.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Spacing.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation N:=(inner_norm (@euclidean_inner_productP R 2)).
Local Notation B:=(@euclidean_inner_product R 2).
Local Notation rho:=(@FactorialDiscScales.radius R).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.

(** Source for [circular_disc_small_ball_tangent_spacing]:
    actual positive q and integer J ensure every original
    parent with j>=J and original a in that parent,
    at every 0<=t<q rho_j, has a local unit tangent
    separating ALL distinct hit child centres by more than
    six child radii. The angular window, late-grid coefficient,
    vertex annulus and every child hit are proved, supporting
    the final density assertion of 3.3.19, p. 306. *)
Theorem circular_disc_small_ball_tangent_spacing:
  exists (q:R) (J:nat),0<q /\forall j (z a:E) (t:R),
  (J<=j)%N ->z \in H j ->A a ->metric_closed_ball z (rho j) a ->
  0<=t ->t<q* rho j ->exists e:E,N e= 1 /\forall k l:'I_(j+4),
  k!=l ->
  (metric_closed_ball (circular_disc_child_center z (rho j) k) (rho j.+1) `&` metric_closed_ball a t)!=set0 ->
  (metric_closed_ball (circular_disc_child_center z (rho j) l) (rho j.+1) `&` metric_closed_ball a t)!=set0 ->
  6* rho j.+1<`|B (circular_disc_child_center z (rho j) k-circular_disc_child_center z (rho j) l) e|.
Proof.
have [kappa [w [q [J [hK [hK1 [hw [hwp [hq [hGap [hSecant hLate]]]]]]]]]]]:=
  @circular_tangent_packing_window_exists R.
exists q,J;split=>// j z a t hj hz ha haBall ht htSmall.
have hIndex:(J<=j+4)%N:= leq_trans hj (leq_addr 4 j).
have [hn [hNq hCoefficient]]:= hLate _ hIndex.
pose r:= rho j.
have hr:0<r:= @factorial_disc_radius_positive R (@FactorialDiscScales.count R) rho
  (@FactorialDiscScales.laws R) j.
have [hDeficit hUpper]:= @circular_disc_original_parent_annulus R H hH A hA j z a hz ha haBall.
pose d:= N (a-z).
have hNP:0<((j+4)%:R:R) by rewrite ltr0n addn_gt0 orbT.
have hN4:(4<=(j+4)%:R:>R) by rewrite ler_nat.
have hQuarter:((j+4)%:R:R)^-1<=1/4.
  rewrite -[X in X<=_]div1r ler_pdivrMr //;lra.
have hdHalf:r/2<=d.
  have hProduct:= ler_wpM2l (ltW hr) hQuarter.
  change (is_true (r-2* r/(j+4)%:R<=d)) in hDeficit;nra.
have hd:0<d by lra.
have hdN:d!=0 by rewrite gt_eqF.
pose eta:= inner_unit_normalization (@euclidean_inner_productP R 2) (a-z).
have hEta:N eta= 1:= inner_unit_normalization_norm hd.
have hVertex:a= z+d*:eta.
  rewrite /eta /inner_unit_normalization -/d scalerA mulfV // scale1r.
  by rewrite addrC subrK.
have [u [hu0 [hu2 hU]]]:= @circular_unit_vector_surjective R eta hEta.
have [theta [hTheta [hThetaUpper hThetaU]]]:= @circular_angle_central_representative R u hu0 hu2.
have hValue:eta= circular_unit_vector theta by rewrite hThetaU hU.
rewrite hValue in hVertex.
pose e:= circular_unit_vector_velocity theta.
exists e;split;first exact:circular_unit_vector_velocity_norm.
move=>k l hDifferent hHitK hHitL.
rewrite (factorial_disc_radius_step (@FactorialDiscScales.laws R)) in hHitK hHitL *.
have hw0:0<=w:= ltW hw.
have hKWindow:= @circular_child_hit_angle_window R z a r d t q w theta (j+4)%N k
  hr hn hVertex hDeficit hUpper hTheta hThetaUpper hw0 hwp hq hGap hNq htSmall hHitK.
have hLWindow:= @circular_child_hit_angle_window R z a r d t q w theta (j+4)%N l
  hr hn hVertex hDeficit hUpper hTheta hThetaUpper hw0 hwp hq hGap hNq htSmall hHitL.
exact:(@circular_child_tangent_strict_separation R z r theta kappa w (j+4)%N k l
  hr hn hK hSecant hCoefficient hDifferent hKWindow hLWindow).
Qed.
End Spacing.
