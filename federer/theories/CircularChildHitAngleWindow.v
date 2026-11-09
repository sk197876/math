(** Federer (1969), 3.3.19, p. 306: child
    discs meeting a sufficiently small original ball
    have their actual angles in a proved local window. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerProductUP Bilinear InnerNorm InnerNormInequalities InnerMetric
  InnerNearbyRadialDirections MetricClosedBalls RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed
  CircularUnitVectors CircularRegularDirections CircularDiscRefinement CircularAngleLift CyclicGridShiftSeparation
  CircularCosineArcOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Window.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation N:=(inner_norm (@euclidean_inner_productP R 2)).
Local Notation B:=(@euclidean_inner_product R 2).
Local Notation hE:=(@euclidean_inner_productP R 2).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation C:=(@CircularTrigonometry.cosine R).

(** Source for [circular_child_hit_angle_window]: a local
    cosine margin 6q<1-cos(w), original t<qr and
    original 1/n<q place the actual lifted angle of
    every child disc meeting B(a,t) in [-w,w]
    about the original radial direction at a. Original
    annular vertex bounds discharge the geometry, supporting
    the final upper-density assertion of 3.3.19, p. 306. *)
Theorem circular_child_hit_angle_window (z a:E) (r d t q w theta:R) n (k:'I_n):
  0<r ->(4<=n)%N ->a= z+d*:(circular_unit_vector theta) ->
  r-2* r/n%:R<=d ->d<=r ->p<=theta ->theta<=3* p ->
  0<=w ->w<=p ->0<q ->6* q<1-C w ->
  (n%:R:R)^-1<q ->t<q* r ->
  (metric_closed_ball (circular_disc_child_center z r k) (r/n%:R) `&` metric_closed_ball a t)!=set0 ->
  `|cyclic_grid_shifted_point (2* p/n%:R) (circular_angle_lift_branch theta) k-theta|<=w.
Proof.
move=>hr hn hVertex hDeficit hdUpper hTheta hThetaUpper hw hwp hq hGap hNq ht [x [hxChild hxBall]].
have hnP:(0<n)%N:= leq_trans (erefl true:(1<=4)%N) hn.
have hNP:0<(n%:R:R) by rewrite ltr0n.
have hN4:(4<=n%:R:>R) by rewrite ler_nat.
have hQuarter:(n%:R:R)^-1<=1/4.
  rewrite -[X in X<=_]div1r ler_pdivrMr //;lra.
pose h:= r/n%:R.
pose c:=(1-n%:R^-1)* r.
have hCentre:c= r-h by rewrite /c /h;ring.
have hc:0<c by rewrite /c mulr_gt0 //;lra.
have hHalf:r/2<=c.
  have hProduct:= ler_wpM2l (ltW hr) hQuarter.
  rewrite /c;nra.
have hD: `|d-c|<=h.
  rewrite ler_norml hCentre /h;apply/andP;split;nra.
have hNear:mdist (z+c*:(@circular_regular_direction R n k)) a<=t+h.
  have hTriangle:= metric_triangle (circular_disc_child_center z r k) x a.
  have hx1:mdist (circular_disc_child_center z r k) x<=h:= hxChild.
  have hx2:mdist x a<=t by rewrite metric_sym;exact:hxBall.
  change (is_true (mdist (circular_disc_child_center z r k) a<=t+h));lra.
have hDirection:= @inner_nearby_radial_directions_bound R (R_n R 2) B hE z a
  (@circular_regular_direction R n k) (circular_unit_vector theta) d c t h
  (@circular_unit_vector_norm R theta) hVertex hc hD hNear.
have hNorm0:0<=N ((@circular_regular_direction R n k)-circular_unit_vector theta):= inner_norm_nonnegative hE _.
have hScale:= ler_wpM2r hNorm0 hHalf.
have hSmallh:h<r* q by rewrite /h ltr_pM2l.
have hNormSmall:N ((@circular_regular_direction R n k)-circular_unit_vector theta)<6* q by nra.
have hCauchy:= inner_cauchy hE ((@circular_regular_direction R n k)-circular_unit_vector theta)
  (circular_unit_vector theta).
rewrite circular_unit_vector_norm mulr1 (bilBl (inner_bilinear hE))
  !circular_unit_vector_inner subrr (real_cosine_zero (circular_trig_basic (@CircularTrigonometry.laws R))) in hCauchy.
have hAbs:`|C (2* p* k%:R/n%:R-theta)-1|<6* q:= le_lt_trans hCauchy hNormSmall.
rewrite ltr_norml in hAbs.
have /andP[hLower _]:= hAbs.
have hCos:C w<=C (2* p* k%:R/n%:R-theta) by lra.
have hLift:= @circular_angle_lift_cosine R n theta k hnP.
have [hLeft hRight]:= @circular_angle_lift_bounds R n theta k hnP hTheta hThetaUpper.
apply:(@circular_cosine_arc_order R _ w hLeft hRight hw hwp).1.
by rewrite hLift.
Qed.
End Window.
