(** Federer (1969), 3.3.19, p. 306: strictly
    more than six child radii separate the actual
    tangential coordinates of nearby original child centres. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerProductUP Bilinear
  InnerNorm InnerMetric CircularTrigonometrySealed CircularUnitVectors CircularUnitCurve
  CircularDiscRefinement CircularAngleLift CyclicGridShiftSeparation CircularTangentCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Separation.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation B:=(@euclidean_inner_product R 2).
Local Notation hE:=(@euclidean_inner_productP R 2).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation S:=(@CircularTrigonometry.sine R).

(** Source for [circular_child_tangent_difference]: the
    actual tangent-coordinate difference of two original
    child centres is (1-1/n)r times the corresponding
    lifted sine difference. This supports the final
    density estimate of 3.3.19, p. 306. *)
Lemma circular_child_tangent_difference (z:E) (r a:R) n (k l:'I_n):
  (0<n)%N ->
  B (circular_disc_child_center z r k-circular_disc_child_center z r l)
    (circular_unit_vector_velocity a)=
  ((1-n%:R^-1)* r)*
    (S (cyclic_grid_shifted_point (2* p/n%:R) (circular_angle_lift_branch a) k-a)-
     S (cyclic_grid_shifted_point (2* p/n%:R) (circular_angle_lift_branch a) l-a)).
Proof.
move=>hn.
rewrite (bilBl (inner_bilinear hE)) /circular_disc_child_center
  !(bilDl (inner_bilinear hE)) !(bilZl (inner_bilinear hE)).
rewrite !circular_unit_vector_tangent_coordinate !circular_angle_lift_sine //.
change (B z (circular_unit_vector_velocity a)+((1-n%:R^-1)* r)* S (2* p* k%:R/n%:R-a)-
  (B z (circular_unit_vector_velocity a)+((1-n%:R^-1)* r)* S (2* p* l%:R/n%:R-a))=
  ((1-n%:R^-1)* r)*(S (2* p* k%:R/n%:R-a)-S (2* p* l%:R/n%:R-a))).
ring.
Qed.

(** Source for [circular_child_tangent_strict_separation]:
    local scalar secant laws and the ACTUAL cyclic
    step give tangent-coordinate separation >6r/n for
    distinct original indices whose local lifted angles
    lie in the proved small window. The displayed
    coefficient is obtained from pi>3 and late n;
    it is an auxiliary cutoff condition, supporting
    3.3.19, p. 306, not a new example hypothesis. *)
Theorem circular_child_tangent_strict_separation (z:E) (r a kappa d:R) n (k l:'I_n):
  0<r ->(4<=n)%N ->0<kappa ->
  (forall u v:R,`|u|<=d ->`|v|<=d ->kappa*`|u-v|<=`|S u-S v|) ->
  6<2* p* kappa*(1-n%:R^-1) ->k!=l ->
  `|cyclic_grid_shifted_point (2* p/n%:R) (circular_angle_lift_branch a) k-a|<=d ->
  `|cyclic_grid_shifted_point (2* p/n%:R) (circular_angle_lift_branch a) l-a|<=d ->
  6*(r/n%:R)<`|B (circular_disc_child_center z r k-circular_disc_child_center z r l)
    (circular_unit_vector_velocity a)|.
Proof.
move=>hr hn hK hSecant hCoefficient hDifferent hk hl.
have hnP:(0<n)%N:= leq_trans (erefl true:(1<=4)%N) hn.
have hNP:0<(n%:R:R) by rewrite ltr0n.
have hNN:(n%:R:R)!=0 by rewrite gt_eqF.
have hN4:(4<=n%:R:>R) by rewrite ler_nat.
have hQuarter:(n%:R:R)^-1<=1/4.
  rewrite -[X in X<=_]div1r ler_pdivrMr //;lra.
have hRadius:0<(1-n%:R^-1)* r by rewrite mulr_gt0 //;lra.
pose q:= 2* p/n%:R.
have hp:= RealTrigonometryUP.real_trigonometry_pi_positive
  (CircularTrigonometryUP.circular_trig_basic (@CircularTrigonometry.laws R)).
have hq:0<q by rewrite /q divr_gt0 //;nra.
have hGap:= @cyclic_grid_shift_separation R q n (circular_angle_lift_branch a) k l hq hDifferent.
pose tk:= cyclic_grid_shifted_point q (circular_angle_lift_branch a) k-a.
pose tl:= cyclic_grid_shifted_point q (circular_angle_lift_branch a) l-a.
have hAngle:tk-tl= cyclic_grid_shifted_point q (circular_angle_lift_branch a) k-
  cyclic_grid_shifted_point q (circular_angle_lift_branch a) l by rewrite /tk /tl;ring.
have hSine:= hSecant tk tl hk hl.
rewrite hAngle in hSine.
have hScaled:= ler_wpM2l (ltW hK) hGap.
have hLower:= le_trans hScaled hSine.
have hProduct:= ler_wpM2l (ltW hRadius) hLower.
have hChild:0<r/n%:R by rewrite divr_gt0.
have hStrict:6*(r/n%:R)<(2* p* kappa*(1-n%:R^-1))*(r/n%:R) by rewrite ltr_pM2r.
have hScalar:(2* p* kappa*(1-n%:R^-1))*(r/n%:R)=((1-n%:R^-1)* r)*(kappa* q) by rewrite /q;field.
rewrite hScalar in hStrict.
rewrite circular_child_tangent_difference // normrM (ger0_norm (ltW hRadius)).
exact:(lt_le_trans hStrict hProduct).
Qed.
End Separation.
