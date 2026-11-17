(** Federer 3.2.45, p. 279: test the printed normalized
    exponent estimate on an actual unit segment in R^3.
    All measure values and projection constants come from the
    previously proved original interfaces. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanCoordinateMetric EuclideanBallVolume RectifiableSetUP CoordinateUnitSegment
  RectifiableGeometricMeasureEquality IntegralGeometricMeasure ProjectionMeasure ProjectionBeta
  ProjectionThreeOneMoment RealPower RealPowerHalfNatural.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Close Scope ereal_scope.

(** Source for [unit_segment_convex_exponent_values]: supporting
    actual-set test of the estimate in Federer 3.2.45,
    p. 279. Every convex integral-geometric exponent measures
    the unit coordinate segment as one, by the full original
    rectifiable equality of 3.2.26, pp. 261-262. *)
Lemma unit_segment_convex_exponent_values (R:realType) (hmn:(1<= 3)%N)
    (t: \bar R):
  (1<=t)%E ->
  @convex_integral_geometric_measure R 3 1 hmn t
    (@euclidean_coordinate_line R 3 ord0 0 @` `[(0%R:R),1%R])= 1%E.
Proof.
move=> ht.
have hRect:=@coordinate_unit_segment_measure_rectifiable R 3 ord0 0.
have hAll:=@federer_3_2_26 R 1 3 hmn _ hRect.
have hQ:=(hAll.2.2.2 t ht).1.
by rewrite coordinate_unit_segment_hausdorff_mass in hQ.
Qed.

(** Source for [convex_exponent_printed_coarse_gamma_one]: the
    literal coarse gamma=alpha(1) 2^(-1) 1! permitted in
    Federer 3.2.45, p. 279, equals one. This calculation
    uses the actual original one-dimensional unit-ball volume. *)
Lemma convex_exponent_printed_coarse_gamma_one (R:realType):
  euclidean_unit_ball_volume R 1/(2:R)^+1*(1%N`!)%:R= 1.
Proof. by rewrite euclidean_unit_ball_volume1 /= !mulr1 divff ?pnatr_eq0. Qed.

(** Source for [convex_exponent_secant_counterexample]: correction
    test for the final quantitative estimate on Federer p. 279,
    3.2.45. For n= 3,m= 1,u=0,v= 1/2 and the actual unit
    segment, every original Q_t value is one, beta_1= 1/2
    and beta_2^2= 1/3. The normalized ratio exceeds the
    displayed upper bound sqrt(2). This concerns that estimate;
    it does not refute the continuity theorem. *)
Theorem convex_exponent_secant_counterexample (R:realType) (hmn:(1<= 3)%N):
  (forall t: \bar R,(1<=t)%E ->
    @convex_integral_geometric_measure R 3 1 hmn t
      (@euclidean_coordinate_line R 3 ord0 0 @` `[(0%R:R),1%R])= 1%E) /\
  real_power ((euclidean_unit_ball_volume R 1/(2:R)^+1*(1%N`!)%:R)/
    (@projection_beta R 3 1 hmn (1:R)%:E)) (1/2)<
    (@projection_beta R 3 1 hmn (2:R)%:E)^-1.
Proof.
split;first exact:unit_segment_convex_exponent_values.
rewrite convex_exponent_printed_coarse_gamma_one projection_three_one_first.
have hTwo:(0<2:>R) by lra.
have hSimpl:(1/(1/2):R)= 2 by field;lra.
rewrite hSimpl (real_power_positive_square_root hTwo).
have htE:(1<=(2:R)%:E)%E by rewrite lee_fin;by lra.
have hBetaPos:=@projection_beta_positive R 3 1 hmn (2:R)%:E htE.
have hSquare:=@projection_three_one_second R hmn.
have hInvSquare:((@projection_beta R 3 1 hmn (2:R)%:E)^-1)^+2= 3.
  rewrite exprVn hSquare;field;lra.
rewrite -(ltr_sqr _ _) ?nnegrE ?sqrtr_ge0 ?invr_ge0 ?(ltW hBetaPos) //
  sqr_sqrtr ?(ltW hTwo) // hInvSquare;by lra.
Qed.
