(** Federer (1969), 3.3.19, p. 305: each actual child
    radial image has an angular representative close to its
    original centre angle. Only local angle witnesses are used. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric MetricClosedBalls
  CircularTrigonometrySealed CircularUnitVectors CircularUnitVectorSurjection CircularAngleLift
  CyclicGridShiftSeparation CircularDiscRefinement CircularDiscRadialDirection CircularDiscRadialAngle.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Parameters.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation p:=(@CircularTrigonometry.half_period R).

(** Source for [circular_disc_radial_parameter_near_centre]:
    every original eta_n(x), for x in a closed original
    child disc, has a parameter within pi/(2n) of that
    child's original 2pi k/n. This is the literal actual
    angular-width input for 3.3.19, p. 305. The
    representative need not lie in the principal period. *)
Theorem circular_disc_radial_parameter_near_centre (z:E) (r:R) n (k:'I_n) (x:E):
  0<r ->(4<=n)%N ->
  metric_closed_ball (circular_disc_child_center z r k) (r/n%:R) x ->
  exists b:R,`|b-2* p* k%:R/n%:R|<p/(2* n%:R) /\
    circular_disc_radial_direction z x= circular_unit_vector b.
Proof.
move=>hr hn hx.
have hUnit:= @circular_disc_radial_direction_unit R z r n k x hr hn hx.
have [t [ht0 [ht2 hT]]]:= @circular_unit_vector_surjective R
  (circular_disc_radial_direction z x) hUnit.
have [a [hpa [hap hA]]]:= @circular_angle_central_representative R t ht0 ht2.
have hAngle:circular_disc_radial_direction z x= circular_unit_vector a by rewrite hA hT.
have hNear:= @circular_disc_child_radial_angle R z r n k x a hr hn hx hAngle hpa hap.
have hNP:(0<n%:R:>R) by rewrite ltr0n;exact:(leq_trans (erefl true : (1<=4)%N) hn).
have hNN:(n%:R:R)!=0 by rewrite gt_eqF.
pose q:R:= 2* p/n%:R.
have hBudget:q* n%:R= 2* p by rewrite /q divfK.
have hTheta:q* k%:R= 2* p* k%:R/n%:R by rewrite /q;ring.
rewrite /cyclic_grid_shifted_point -/q in hNear.
case hBranch:(circular_angle_lift_branch a k).
- rewrite hBranch /= mulrDr hBudget in hNear.
  exists (a-(p+p));split.
  + have hDifference:a-(p+p)-2* p* k%:R/n%:R= -(q* k%:R+2* p-a) by rewrite -hTheta;ring.
    by rewrite hDifference normrN.
  + have hPeriod:= @circular_unit_vector_period R (a-(p+p)).
    rewrite subrK in hPeriod.
    by rewrite -hPeriod.
- rewrite hBranch /= addr0 in hNear.
  exists a;split=>//.
  by rewrite -hTheta -[a-q* k%:R]opprB normrN.
Qed.
End Parameters.
