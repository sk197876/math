(** Federer (1969), 3.3.19, p. 304:
    the original circular-disc set has H1 mass two
    and beta_t Q_t^1 mass two for every exponent.
    Here Q is the convex-cover measure; ordinary
    all-Borel I is not substituted for it. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric CircularTrigonometrySealed CircularUnitCircleLength
  CircularDiscTreeUP CircularDiscLimitUP CircularDiscHausdorffUpper CircularDiscFirstConvexMassLower
  IntegralGeometricMeasure IntegralGeometricInfinity IntegralGeometricExponentMonotone
  CaratheodoryProjectionLength HausdorffMeasure ProjectionBeta UnitBallIntrinsicVolume EuclideanBallVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Mass.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation beta:=(@projection_beta R 2 1 (leqnSn 1)).
Local Notation Q:=(@convex_integral_geometric_measure R 2 1 (leqnSn 1)).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.

(** Source for [circular_disc_first_beta_normalization]:
    beta_1(2,1) pi= 2, the exact
    coefficient in the comparison chain of
    3.3.19, p. 304. This follows
    from the proved actual unit-ball Cauchy
    coefficient and actual alpha(2)= pi. *)
Lemma circular_disc_first_beta_normalization:beta 1* p= 2.
Proof.
have h:= @unit_ball_cauchy_coefficient R 1.
rewrite (@circular_half_period_planar_volume R) (@euclidean_unit_ball_volume1 R) in h.
change (2* p* beta 1= 2*2) in h;nra.
Qed.

(** Source for [circular_disc_normalized_convex_mass]:
    beta_t(2,1) Q_t^1(A)= 2 for every
    1<=t<=infinity, exactly the displayed
    conclusion of 3.3.19, p. 304.
    The original cover lower bound and Hausdorff
    upper bound squeeze the whole exponent family. *)
Theorem circular_disc_normalized_convex_mass (t: \bar R):(1<=t)%E ->
  ((beta t)%:E* Q t A=(2:R)%:E)%E.
Proof.
move=>ht.
have hLower:= @circular_disc_first_convex_mass_lower R H hH A hA.
have hPositive:0<beta 1:= @projection_beta_positive R 2 1 (leqnSn 1) 1 (lexx _).
have hWeighted:= lee_wpmul2l (lee_tofin (ltW hPositive)) hLower.
rewrite -EFinM circular_disc_first_beta_normalization in hWeighted.
have hMonotone:= @convex_integral_geometric_normalized_measure_monotone R 2 1 (leqnSn 1) 1 t A (lexx _) ht.
have hUpper:= @convex_integral_geometric_normalized_measure_monotone R 2 1 (leqnSn 1) t +oo A ht (leey _).
rewrite projection_beta_infinity mul1e convex_integral_geometric_infinity
  (@caratheodory_projection_one_hausdorff_measure R 2 A (erefl true)) in hUpper.
have hHausdorff:= @circular_disc_limit_Hausdorff_upper R H A hH hA.
apply/eqP;rewrite eq_le;apply/andP;split.
- exact:(le_trans hUpper hHausdorff).
- exact:(le_trans hWeighted hMonotone).
Qed.

(** Source for [circular_disc_hausdorff_mass]: the
    original H^1(A)= 2 in 3.3.19,
    p. 304. The infinity member of
    the proved convex exponent family equals the
    actual Hausdorff measure of the unchanged A. *)
Theorem circular_disc_hausdorff_mass:@hausdorff_measure R E 1 A=(2:R)%:E.
Proof.
have h:= circular_disc_normalized_convex_mass (leey 1).
by rewrite projection_beta_infinity mul1e convex_integral_geometric_infinity
  (@caratheodory_projection_one_hausdorff_measure R 2 A (erefl true)) in h.
Qed.

(** Source for [circular_disc_first_convex_mass]:
    Q_1^1(A)= pi, the second exact
    measure value in 3.3.19, p. 304.
    The actual positive finite beta cancels from
    its normalized identity; no finiteness premise. *)
Theorem circular_disc_first_convex_mass:Q 1 A= p%:E.
Proof.
have h:= @circular_disc_normalized_convex_mass 1 (lexx _).
have hExpected:((beta 1)%:E* p%:E=(2:R)%:E)%E.
  by rewrite -EFinM circular_disc_first_beta_normalization.
have hEqual:= eq_trans h (esym hExpected).
have hPositive:0<beta 1:= @projection_beta_positive R 2 1 (leqnSn 1) 1 (lexx _).
have hNonzero:beta 1!=0 by rewrite gt_eqF.
have hCancel (z: \bar R):(((beta 1)^-1)%:E*((beta 1)%:E* z)= z)%E.
  by rewrite muleA -EFinM mulVf // mul1e.
have hScaled:= congr1 (fun z: \bar R=>(((beta 1)^-1)%:E* z)%E) hEqual.
by rewrite !hCancel in hScaled.
Qed.
End Mass.
