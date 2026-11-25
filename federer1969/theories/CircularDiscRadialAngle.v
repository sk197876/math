(** Federer (1969), 3.3.19, p. 305: the actual radial
    direction of every original child-disc point lies within
    half an angular half-step of that child's direction. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric MetricClosedBalls InnerRadialBallSquare
  RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed CircularUnitVectors
  CircularDiscRefinement CircularDiscRadialDirection CircularRadialAngleBound
  CircularAngleLift CyclicGridShiftSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Geometry.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation hE:=(@euclidean_inner_productP R 2).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation C:=(@CircularTrigonometry.cosine R).

(** Source for [positive_radius_polar_square_scale]: divide
    the actual squared child-disc inequality by its positive
    radius squared, supporting the angular estimate in
    3.3.19, p. 305. *)
Lemma positive_radius_polar_square_scale (e d v c:R):
  0<e ->d^+2+(e* v)^+2-2* d*(e* v)* c<=e^+2 ->
  (d/e)^+2+v^+2-2*(d/e)* v* c<=1.
Proof.
move=>he hSquare.
have heN:e!=0 by rewrite gt_eqF.
have heSq:0<e^+2 by rewrite exprn_gt0.
have hIdentity:e^+2*((d/e)^+2+v^+2-2*(d/e)* v* c)=
  d^+2+(e* v)^+2-2* d*(e* v)* c by field.
by rewrite -(ler_pM2l heSq) hIdentity mulr1.
Qed.

(** Source for [circular_disc_child_radial_angle]: actual
    eta_n(x) and original child direction differ by less
    than pi/(2n) after a local period lift, supporting
    the original angular counts in 3.3.19, p. 305.
    All closed-disc points and boundary contacts remain. *)
Theorem circular_disc_child_radial_angle (z:E) (r:R) n (k:'I_n) (x:E) (a:R):
  0<r ->(4<=n)%N ->
  metric_closed_ball (circular_disc_child_center z r k) (r/n%:R) x ->
  circular_disc_radial_direction z x= circular_unit_vector a ->
  p<=a ->a<=3* p ->
  `|cyclic_grid_shifted_point (2* p/n%:R) (circular_angle_lift_branch a) k-a|<p/(2* n%:R).
Proof.
move=>hr hn hx hAngle hpa hap.
have hNP:(0<n%:R:>R) by rewrite ltr0n;exact:(leq_trans (erefl true : (1<=4)%N) hn).
have hNN:(n%:R:R)!=0 by rewrite gt_eqF.
have hnP:(0<n)%N by rewrite -(@ltr0n R).
pose e:R:= r/n%:R.
pose v:R:= n%:R-1.
pose d:R:= inner_norm hE (x-z).
have he:0<e by rewrite /e divr_gt0.
have hd:0<d:= @circular_disc_child_parent_radius_positive R z r n k x hr hn hx.
have hBudget:(n%:R:R)* n%:R^-1= 1 by rewrite mulfV.
have hCentreScale:(1-n%:R^-1)* r= e* v by rewrite /e /v;nra.
have hPolar:= @inner_radial_ball_square R (R_n R 2) (@euclidean_inner_product R 2) hE
  z (circular_unit_vector (2* p* k%:R/n%:R)) x ((1-n%:R^-1)* r)
  (@circular_unit_vector_norm R _) hd.
change (mdist (circular_disc_child_center z r k) x^+2=
  d^+2+((1-n%:R^-1)* r)^+2-2*((1-n%:R^-1)* r)* d*
    euclidean_inner_product (circular_unit_vector (2* p* k%:R/n%:R))
      (circular_disc_radial_direction z x)) in hPolar.
rewrite hAngle circular_unit_vector_inner hCentreScale in hPolar.
have hSquared:mdist (circular_disc_child_center z r k) x^+2<=e^+2.
  rewrite (ler_sqr (mdist_ge0 _ _) (ltW he));exact hx.
rewrite hPolar in hSquared.
have hSquaredOrder:d^+2+(e* v)^+2-2* d*(e* v)* C (2* p* k%:R/n%:R-a)<=e^+2 by nra.
have hScaled:= positive_radius_polar_square_scale he hSquaredOrder.
have hLift:= @circular_angle_lift_cosine R n a k hnP.
rewrite -hLift in hScaled.
have [hLower hUpper]:= @circular_angle_lift_bounds R n a k hnP hpa hap.
have hD:0<d/e by rewrite divr_gt0.
exact:(@circular_radial_angle_bound R n (d/e)
  (cyclic_grid_shifted_point (2* p/n%:R) (circular_angle_lift_branch a) k-a)
  hn hD hLower hUpper hScaled).
Qed.
End Geometry.
